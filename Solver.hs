module Solver where

import Control.Arrow ((***))
import Data.List
import Data.Char
import Data.Maybe (catMaybes)

import Types
import WordData
import Clues
import Examples

------------------------------------------------------
-- Part I

punctuation :: String
punctuation 
  = "';.,-!?"

cleanUp :: String -> String
cleanUp s
  = [toLower c | c <- s, c `notElem` punctuation]

split2 :: [a] -> [([a], [a])]
split2 xs
  = [splitAt i xs | i <- [1 .. length xs - 1]] 

split3 :: [a] -> [([a], [a], [a])]
split3 xs
  = [ (pre, mid, suf)
    | (pre, suf') <- split2 xs
    , (mid, suf) <- ([], suf') : split2 suf'
    ]

uninsert :: [a] -> [([a], [a])]
uninsert xs
  = [(mid, pre ++ suf) | (pre, mid, suf) <- split3 xs, not (null mid)]

split2M :: [a] -> [([a], [a])]
split2M xs
  = sxs ++ [(y, x) | (x, y) <- sxs] 
  where
    sxs = split2 xs

split3M :: [a] -> [([a], [a], [a])]
split3M xs
  = sxs ++ [(z, y, x) | (x, y, z) <- sxs]
  where
    sxs = split3 xs

------------------------------------------------------
-- Part II

matches :: String -> ParseTree -> Bool
matches s (Synonym s')
  = s `elem` synonyms s'
matches s (Anagram _ s')
  = sort s == sort s'
matches s (Reversal _ t)
  = matches (reverse s) t
matches s (HiddenWord _ s')
  | [w] <- ws
  = s `isInfixOf` inner s'
  | (w1 : _ : _) <- ws
  = or [ pre `isSuffixOf` w1 &&
         suf `isPrefixOf` last ws &&
         mid == concat (inner ws)
       | (pre, mid, suf) <- split3 s
       ]
  where
    ws = words s'
    -- Remove the first and last elements of a list
    inner :: [a] -> [a]
    inner [] = []
    inner (_ : xs) = init xs
-- This technically incorrect solution worked for executing 'solveAll 24':
-- > matches s (HiddenWord _ s') = s `isInfixOf` (concat (words s'))
matches s t
  | Insertion _ t1 t2 <- t
  = matchesSplitUsing uninsert t1 t2 s
  | Charade _ t1 t2 <- t
  = matchesSplitUsing split2   t1 t2 s
  where
    matchesSplitUsing
      :: (String -> [(String, String)])
      -> ParseTree
      -> ParseTree
      -> String
      -> Bool
    matchesSplitUsing f t1 t2 s
      = or (uncurry (&&) . ((`matches` t1) *** (`matches` t2)) <$> f s)
{-
matches s (Insertion _ t1 t2)
  = not $ null [ ()
               | (pre, suf) <- uninsert s
               , matches pre t1
               , matches suf t2
               ]
matches s (Charade _ t1 t2)
  = not $ null [ ()
               | (pre, suf) <- split2 s
               , matches pre t1
               , matches suf t2
               ]
-}

evaluate :: Parse -> Int -> [String]
evaluate (def, _, t) n
  = [ s
    | s <- synonyms (unwords def)
    , length s == n
    , matches s t
    ]

------------------------------------------------------
-- Part III

hasSynonyms :: String -> Bool
hasSynonyms = not . null . synonyms

-- Given...
parseWordplay :: [String] -> [ParseTree]
parseWordplay ws
  = concat ([parseSynonym,
             parseAnagram,
             parseReversal,
             parseInsertion,
             parseCharade,
             parseHiddenWord] <*> pure ws)
    
parseSynonym :: [String] -> [ParseTree]
parseSynonym ss
  | hasSynonyms s
  = [Synonym s]
  | otherwise
  = []
  where
    s = unwords ss

parseUndirectedIndicator
  :: (Indicator -> a -> ParseTree)
  -> ([String] -> [([String], [String])])
  -> ([String] -> [a])
  -> [String]
  -> [String]
  -> [ParseTree]
parseUndirectedIndicator constr splitFun mkArgs inds ss
  = [ constr pre arg
    | (pre, suf) <- splitFun ss
    , unwords pre `elem` inds
    , arg <- mkArgs suf
    ]

parseAnagram :: [String] -> [ParseTree]
parseAnagram
  = parseUndirectedIndicator Anagram split2M (return . concat) anagramIndicators
{-
Before refactor:
parseAnagram ss
  = [ Anagram pre (concat suf)
    | (pre, suf) <- split2M ss
    , unwords pre `elem` anagramIndicators
    ]
-}

parseReversal :: [String] -> [ParseTree]
parseReversal
  = parseUndirectedIndicator Reversal split2M parseWordplay reversalIndicators
{-
Before refactor:
parseReversal ss
  = [ Reversal pre t
    | (pre, suf) <- split2M ss
    , unwords pre `elem` reversalIndicators
    , t <- parseWordplay suf
    ]
-}

parseDirectedIndicator
  :: (Indicator -> ParseTree -> ParseTree -> ParseTree)
  -> [String]
  -> [String]
  -> [String]
  -> [ParseTree]
parseDirectedIndicator constr forwardInds backwardInds ss
  = do
  (pre, ind, suf) <- split3 ss
  let
    [isForward, isBackward]
      = elem (unwords ind) <$> [forwardInds, backwardInds]
  preTree <- parseWordplay pre
  sufTree <- parseWordplay suf
  uncurry (constr ind) <$> catMaybes
    [ if isForward  then Just (preTree, sufTree) else Nothing
    , if isBackward then Just (sufTree, preTree) else Nothing
    ]

parseInsertion :: [String] -> [ParseTree]
parseInsertion
  = parseDirectedIndicator Insertion insertionIndicators envelopeIndicators
{-
Before refactor:
parseInsertion ss
  = [ Insertion ind t1 t2
    | (pre, ind, suf) <- split3 ss
    , unwords ind `elem` insertionIndicators
    , t1 <- parseWordplay pre
    , t2 <- parseWordplay suf
    ] ++
    [ Insertion ind t1 t2
    | (pre, ind, suf) <- split3 ss
    , unwords ind `elem` envelopeIndicators
    , t1 <- parseWordplay suf
    , t2 <- parseWordplay pre
    ]
-}

parseCharade :: [String] -> [ParseTree]
parseCharade
  = parseDirectedIndicator Charade beforeIndicators afterIndicators
{-
Before refactor:
parseCharade ss
  = [ Charade ind t1 t2
    | (pre, ind, suf) <- split3 ss
    , unwords ind `elem` beforeIndicators
    , t1 <- parseWordplay pre
    , t2 <- parseWordplay suf
    ] ++
    [ Charade ind t1 t2
    | (pre, ind, suf) <- split3 ss
    , unwords ind `elem` afterIndicators
    , t1 <- parseWordplay suf
    , t2 <- parseWordplay pre
    ]
-}

parseHiddenWord :: [String] -> [ParseTree]
parseHiddenWord
  = parseUndirectedIndicator HiddenWord split2 (return . unwords) hiddenWordIndicators
{- Before refactor:
parseHiddenWord ss
  = [ HiddenWord ind (unwords suf)
    | (ind, suf) <- split2 ss
    , unwords ind `elem` hiddenWordIndicators
    ]
-}

-- Given...
parseClue :: Clue -> [Parse]
parseClue clue@(s, n)
  = parseClueText (words (cleanUp s))

parseClueText :: [String] -> [Parse]
parseClueText ss
  = [ (def, link, t)
    | (def, link, wp) <- split3M ss
    , unwords link `elem` linkWords
    , hasSynonyms (unwords def)
    , t <- parseWordplay wp
    ]

solve :: Clue -> [Solution]
solve c@(_, n)
  = [ (c, p, s)
    | p <- parseClue c
    , s <- evaluate p n
    ]


------------------------------------------------------
-- Some additional test functions

-- Returns the solution(s) to the first k clues.
-- The nub removes duplicate solutions arising from the
-- charade parsing rule.
solveAll :: Int -> [[String]]
solveAll k
  = map (nub . map getSol . solve . (clues !!)) [0..k-1]

getSol :: Solution -> String
getSol (_, _, sol) = sol

showAll
  = mapM_ (showSolutions . solve . (clues !!)) [0..23]


