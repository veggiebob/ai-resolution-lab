{-

Author:     Jacob Bowman (jb6248@rit.edu)
CSCI 331 Intro to AI - Lab 2

This will be automatically compiled and linked when 
the main file is compiled.

-}

module Lib where

import Data.Bool
import Data.Char
import System.IO
import System.Environment (getArgs)
import Data.Set (Set)
import Data.List (intercalate)
import Data.Maybe (catMaybes)
import Control.Applicative (liftA2)
import qualified Data.Set as Set


-- https://cs.rit.edu/~jro/courses/intelSys/labs/resolution/
-- https://cs.rit.edu/~jro/courses/intelSys/labs/resolution/truck.cnf

-- represents a "substitution"
data Subst a = Subst a a 
    deriving (Eq, Ord) -- substitute a for a
-- concise operator constructor
(/:) :: Symbol -> Symbol -> Subst Symbol
s1 /: s2 = Subst s1 s2


--------------------------------
--       DEFINITIONS          --
--------------------------------


instance (Show a) => Show (Subst a) where
    -- "a replaces b" is shown by "a/b"
    show (Subst a b) = (show a) ++ "/" ++ (show b)


-- unification represents two literals being combined together
-- and seeing if they can be unified, and if so, what kind of
-- substitutions need to be used.
class Unify r where
    -- either give the unified version, or Nothing if they can't be unified
    unify :: r -> r -> Maybe (r, [Subst Symbol])
    -- unify x y = unify y x ??

-- example: Kim or x1 or y2 or Terry or mom_of(Terry) or SKF1(x1)
data Symbol = C String | V String | Function String Symbol
    deriving (Eq, Ord)

instance Show Symbol where
    show (C s) = s
    show (V s) = '_':s
    show (Function n s) = n ++ "(" ++ show s ++ ")"


instance Unify Symbol where
    -- constants only unify if they're equal
    unify (C s1) (C s2) | s1 == s2  = Just $ (C s1, [])
                        | otherwise = Nothing

    unify v@(V _) v2@(V _) = Just (v, [v/:v2]) -- two variables unify together
    unify v@(V _) c@(C _) = Just (c , [v/:c])


    
    unify (Function n1 a1) (Function n2 a2) 
        | n1 == n2  = fmap (\(x, s) -> (Function n1 x, s)) $ unify a1 a2
        | otherwise = Nothing
    unify (Function _ _) (C _) = Nothing -- unless it happens to be true?
                                      -- example: unify(mother_of(Kim), Poppy) knowing that
                                      --          Poppy is actually the mother of Kim??
    unify f@(Function _ v1@(V _)) v2@(V _) | v1 == v2  = Nothing
                                           | otherwise = Just (f, [v2/:f])

    unify x y = unify y x
    
-- the strings are names
-- ex. mom_of(Kim) => Unary "mom_of" (C "Kim")
data Predicate = Nullary String | Unary String Symbol | Binary String Symbol Symbol
    deriving (Eq, Ord)

instance Show Predicate where
    show (Nullary s) = s
    show (Unary n s) = n ++ "(" ++ show s ++ ")"
    show (Binary n a1 a2) = n ++ "(" ++ show a1 ++ ", " ++ show a2 ++ ")"

instance Unify Predicate where

    -- predicates can only be unified if
    -- they have the same ... parity? dimension?
    unify (Unary n1 v1) (Unary n2 v2) 
        | n1 == n2  = fmap (\(x, s) -> (Unary n1 x, s)) $ unify v1 v2
        | otherwise = Nothing

    unify (Binary n1 a1 a2) (Binary n2 b1 b2)
        | n1 == n2  = case (u1, u2) of
                        (Just (u1, s1), Just (u2, s2)) -> 
                            Just (Binary n1 u1 u2, s1 ++ s2)
                        (_, _) -> Nothing
        | otherwise = Nothing
        where   u1 = unify a1 b1
                u2 = unify a2 b2

    unify (Nullary s1) (Nullary s2)
        | s1 == s2  = Just (Nullary s1, [])
        | otherwise = Nothing

    unify _ _ = Nothing

-- not entirely sure if this definition is accurate
-- but "Pos" is just the absence of a negation
data Literal = Neg Predicate | Pos Predicate
    deriving (Eq, Ord)


instance Show Literal where
    show (Neg p) = "~" ++ show p
    show (Pos p) = show p

-- set of negated (or not) predicates
newtype Clause = Clause (Set Literal)       -- logical OR (v)
    deriving (Eq, Ord)

instance Show Clause where
    show (Clause literals) = "{" ++ (intercalate ", " . fmap show . Set.toList) literals ++ "}"

-- whole collection of clauses
newtype Sentence = Sentence (Set Clause)    -- logical AND (^)
    deriving (Eq)

instance Show Sentence where
    show (Sentence clauses) = (intercalate ";\n" . fmap show . Set.toList) clauses

-- get the set of literals from a clause
liftC :: Clause -> Set Literal
liftC (Clause c) = c

-- get the predicate from a literal
getLP :: Literal -> Predicate
getLP (Neg p) = p
getLP (Pos p) = p

-- negate a literal
negL :: Literal -> Literal
negL (Pos p) = Neg p
negL (Neg p) = Pos p

-- check if a clause is empty
clauseEmpty  :: Clause -> Bool
clauseEmpty (Clause s) = Set.null s

-- inference machine
-- loop via recursion
resolution :: Sentence -> (Sentence, Bool)
resolution (Sentence clauses) 
        -- no new sets
    | new `Set.isSubsetOf` clauses = (Sentence new, False)                  
        -- empty set {} is present
    | Set.foldr (||) False (Set.map clauseEmpty mpd) = (Sentence new, True)
        -- append new clauses, iterate again
    | otherwise = resolution $ Sentence new                                 
    where   pairs = Set.cartesianProduct clauses clauses
            mpd = Set.foldr Set.union Set.empty 
                    paired
            paired = Set.map (uncurry resolve) pairs
            new = Set.union clauses mpd


-- takes two clauses and joins them over their common predicates
resolve :: Clause -> Clause -> Set Clause
-- 1. use clause pairs to find substitutions
-- 2. do substitution on both clauses for each pair
-- 3. remove the predicate
resolve c1 c2 = simp . Set.map (Clause . un . sub) $ pairs
    where   simp = Set.fromList . catMaybes . Set.toList . 
                    Set.map simplify
            pairs = clausePairs c1 c2
            un = uncurry Set.union . (\(x,y) -> (liftC x, liftC y))
            sub (subs, pred) = (removePred sc1 pred, removePred sc2 pred)
                where   sc1 = substClause subs c1
                        sc2 = substClause subs c2

-- occasionally, there will be a clause like
-- { n, !p, p }
-- in this case, the duplicates can be removed
-- ==> { n }
simplify :: Clause -> Maybe Clause
simplify (Clause lits) 
    | Set.null last && not (Set.null lits) = Nothing
    | otherwise     = Just . Clause $ last
    where   containsOpp lit = (negL lit) `Set.member` lits
            last = Set.filter (not . containsOpp) $ lits

-- debugging function
rtest :: String -> String -> Set Clause
rtest c1 c2 = resolve (parseClause c1) (parseClause c2)

-- returns Some (sign of lit. removed) or else Nothing if it's not in it
removePred :: Clause -> Predicate -> Clause
removePred (Clause clause) p = Clause $ Set.filter ((/=p) . getLP) clause

-- helpers
clausePairs :: Clause -> Clause -> Set ([Subst Symbol], Predicate)
clausePairs (Clause s1) (Clause s2) = Set.map (\((l1, l2), subs) -> (
                                                subs,
                                                substPred subs (getLP l1) -- or l2??
                                                )) .
                Set.fromList . catMaybes . Set.toList .
                Set.map ((\(lits, sbs) -> fmap ((,) lits) sbs) .  carry un) $ 
                Set.cartesianProduct s1 s2 
    where   un = uncurry litSubs 
            carry f a = (a, f a)

-- give the substitutions necessary if the literals can be joined
litSubs :: Literal -> Literal -> Maybe [Subst Symbol]
litSubs (Pos p) (Neg q) = (fmap snd . unify p) q
litSubs p@(Neg _) q@(Pos _) = litSubs q p
litSubs _ _ = Nothing

-- does substitutions of symbols
substClause :: [Subst Symbol] -> Clause -> Clause
substClause sbs = cmap (substLit sbs)
    where   cmap f (Clause s) = Clause . Set.map f $ s

-- substitution in literals
substLit :: [Subst Symbol] -> Literal -> Literal
substLit sbs = lmap (substPred sbs)
    where   lmap f (Pos p) = (Pos . f) p
            lmap f (Neg p) = (Neg . f) p

-- substitution in predicates
substPred :: [Subst Symbol] -> Predicate -> Predicate
substPred sbs = pmap $ substSym sbs
    where   pmap f (Unary n s) = Unary n (f s)
            pmap f (Binary n a1 a2) = Binary n (f a1) (f a2)
            pmap f nullary = nullary

-- substitute a symbol?
substSym :: [Subst Symbol] -> Symbol -> Symbol
substSym sbs s = (helper . filterSym sbs) s
    where   helper Nothing = s      -- can't be substituted
            helper (Just x) = x            -- take first substitution
            filterSym ((Subst cs ss):xs) s | cs == s   = Just ss
                                           | otherwise = filterSym xs s
            filterSym [] _ = Nothing

-- finds the same predicates between two clauses (only opposites)

-- tells if two literals are opposite sign, but same predicate
opposite :: Literal -> Literal -> Bool
opposite (Neg p) (Pos q) = p == q
opposite p@(Pos _) q@(Neg _) = opposite q p
opposite _ _ = False


----------------------
--    PARSING       --
----------------------

-- all parsing is done assuming that each string
-- is well-formed, so no errors will ever occur

-- file representation type
type FileCNF = (Set String, Set String, Set String, Set String, Set Clause)

-- get each member
cnfPred :: FileCNF -> Set String -- and so on
cnfPred     (p, _, _, _, _) = p
cnfVar      (_, v, _, _, _) = v
cnfConst    (_, _, c, _, _) = c
cnfFuncs    (_, _, _, f, _) = f
cnfClauses  (_, _, _, _, c) = c

-- example file: truck.cnf
parseFile :: String -> FileCNF
parseFile f = convertClauses . getSets . lines $ f 
    where getSets (ln_pred:
                   ln_var:
                   ln_const:
                   ln_funcs:
                   _: -- ignore "Clauses: \n"
                   ln_clauses) = ( 
                             Set.fromList . tail . words $ ln_pred,
                             Set.fromList . tail . words $ ln_var,
                             Set.fromList . tail . words $ ln_const,
                             Set.fromList . tail . words $ ln_funcs,
                             Set.fromList $ ln_clauses
                         )
          convertClauses (a, b, c, d, clauses) = (a, b, c, d, Set.map parseClause clauses)


-- convert string to clause
-- (same as literal but ignores "!")
parseClause :: String -> Clause
parseClause = Clause . Set.fromList . fmap parseLiteral . words

-- convert string to literal (check for not)
parseLiteral :: String -> Literal 
parseLiteral xs = if isNot then Neg p else Pos p
    where   p = case length params of
                    0 -> Nullary pred
                    1 -> Unary pred . head $ params 
                    2 -> Binary pred
                                (head(params))
                                (head(tail(params)))
                    _ -> error "not 1 nor two parameters??"
            isNot = (=='!') . head $ xs
            rest = if isNot then tail xs else xs
            pred = takeWhile isLetter rest
            params' ('(':ps) = fmap parseSymbol . split . init $ ps 
            params' ps = []
            params = params' . drop (length pred) $ rest

-- convert string to predicate
parsePred :: String -> Predicate
parsePred = getLP . parseLiteral

-- convert string to symbol
parseSymbol :: String -> Symbol
parseSymbol s@(x:xs) 
    | ((==')') . last) s = Function (takeWhile (/='(') s) (parseSymbol $ arg s)
    | isUpper x = C s
    | otherwise = V s

    -- get the first arg if it's a function
    where arg = tail . init . dropWhile (/='(')


 
{- a couple string functions -}

split str = case break (==',') str of
                (a, ',':b) -> a : split b
                (a, "")    -> [a]

-- same as python (unused?)
rstrip = reverse . dropWhile (==' ') . reverse

-- map a function over file contents
-- for debugging purposes
useFile :: (Show a) => String -> (String -> a) -> IO ()
useFile fp f = do
    handle <- openFile fp ReadMode
    contents <- hGetContents handle
    putStrLn . show $ f contents

{- Main -}
{- note: these functions are not actually "main" functions.
         see Main.hs -}

-- do resolution on the file and get the derivative
-- clauses as well as the result (was it satisfiable?)
doResolution :: FileCNF -> (Sentence, Bool)
doResolution = resolution . Sentence . cnfClauses

-- map the function over the CNF repr of the contents of the file
main' :: (Show a) => (FileCNF -> a) -> String -> IO ()
main' f filepath = do
    handle <- openFile filepath ReadMode
    contents <- hGetContents handle
--    putStrLn contents
    putStrLn . show . f $ parseFile contents
    hClose handle
    return ()


-- do resolution on the contents of the file at the path 
cmain' :: String -> IO ()
cmain' fp = do
    main' (not . snd . doResolution) fp
