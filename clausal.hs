type AtomicSentence = String
type Clause = [Literal]
data Literal = LiteralAtomicSentence AtomicSentence | LiteralNegationAtomicSentence AtomicSentence deriving (Show)
data LogicTree = Leaf AtomicSentence
               | Not LogicTree
               | And LogicTree LogicTree
               | Or LogicTree LogicTree
               | Implies LogicTree LogicTree
               | Equivalence LogicTree LogicTree
               deriving (Show)

implicationsOut :: LogicTree -> LogicTree
implicationsOut (Implies a b) = Or (Not (implicationsOut a)) (implicationsOut b)
implicationsOut (Equivalence a b) = And (Or (Not (implicationsOut a)) (implicationsOut b)) (Or (Not (implicationsOut b)) (implicationsOut a))
implicationsOut (And a b) = And (implicationsOut a) (implicationsOut b)
implicationsOut (Or a b) = Or (implicationsOut a) (implicationsOut b)
implicationsOut (Not a) = Not (implicationsOut a)
implicationsOut (Leaf a) = Leaf a

removeDoubleNegations :: LogicTree -> LogicTree
removeDoubleNegations (Not (Not a)) = removeDoubleNegations a
removeDoubleNegations (Not a) = Not (removeDoubleNegations a)
removeDoubleNegations (And a b) = And (removeDoubleNegations a) (removeDoubleNegations b)
removeDoubleNegations (Or a b) = Or (removeDoubleNegations a) (removeDoubleNegations b)
removeDoubleNegations (Implies a b) = Implies (removeDoubleNegations a) (removeDoubleNegations b)
removeDoubleNegations (Equivalence a b) = Equivalence (removeDoubleNegations a) (removeDoubleNegations b)
removeDoubleNegations (Leaf a) = Leaf a

negationsIn :: LogicTree -> LogicTree
negationsIn (Not (And a b)) = Or (negationsIn (Not a)) (negationsIn (Not b))
negationsIn (Not (Or a b)) = And (negationsIn (Not a)) (negationsIn (Not b))
negationsIn (Not a) = Not (negationsIn a)
negationsIn (And a b) = And (negationsIn a) (negationsIn b)
negationsIn (Or a b) = Or (negationsIn a) (negationsIn b)
negationsIn (Implies a b) = Implies (negationsIn a) (negationsIn b)
negationsIn (Equivalence a b) = Equivalence (negationsIn a) (negationsIn b)
negationsIn (Leaf a) = Leaf a

distribution :: LogicTree -> LogicTree
distribution (Or a (And b c)) = And (distribution (Or a b)) (distribution (Or a c))
distribution (Or (And a b) c) = distribution (Or c (And a b))
distribution (Or a b) = Or (distribution a) (distribution b)
distribution (And a b) = And (distribution a) (distribution b)
distribution (Implies a b) = Implies (distribution a) (distribution b)
distribution (Equivalence a b) = Equivalence (distribution a) (distribution b)
distribution (Not a) = Not (distribution a)
distribution (Leaf a) = Leaf a

-- aka toClauses
-- there's probably a more concise way of writing this
-- leaf / not leaf could be made a type (?)
operatorsOut :: LogicTree -> [Clause]
operatorsOut = operatorsOutR
  where
    operatorsOutR :: LogicTree -> [Clause]
    operatorsOutR (Or a b) = [flattenOrTree (Or a b)]
    operatorsOutR (And (Leaf a) (Leaf b)) = [[LiteralAtomicSentence a],[LiteralAtomicSentence b]]
    operatorsOutR (And (Not (Leaf a)) (Leaf b)) = [[LiteralNegationAtomicSentence a],[LiteralAtomicSentence b]]
    operatorsOutR (And (Leaf a) (Not (Leaf b))) = [[LiteralAtomicSentence a],[LiteralNegationAtomicSentence b]]
    operatorsOutR (And (Not (Leaf a)) (Not (Leaf b))) = [[LiteralNegationAtomicSentence a],[LiteralNegationAtomicSentence b]]
    operatorsOutR (And (Or a b) (Leaf c)) = [flattenOrTree (Or a b)] ++ [[LiteralAtomicSentence c]]
    operatorsOutR (And (Or a b) (Not (Leaf c))) = [flattenOrTree (Or a b)] ++ [[LiteralNegationAtomicSentence c]]
    operatorsOutR (And (Leaf a) (Or b c)) = [[LiteralAtomicSentence a]] ++ [flattenOrTree (Or b c)]
    operatorsOutR (And (Not (Leaf a)) (Or b c)) = [[LiteralNegationAtomicSentence a]] ++ [flattenOrTree (Or b c)]
    operatorsOutR (And (Or a b) (Or c d)) = [flattenOrTree (Or a b)] ++ [flattenOrTree (Or c d)]
    operatorsOutR (And (And a b) (Leaf c)) = operatorsOutR (And a b) ++ [[LiteralAtomicSentence c]]
    operatorsOutR (And (And a b) (Not (Leaf c))) = operatorsOutR (And a b) ++ [[LiteralNegationAtomicSentence c]]
    operatorsOutR (And (And a b) (And c d)) = operatorsOutR (And a b) ++ operatorsOutR (And c d)
    operatorsOutR (And (And a b) (Or c d)) = operatorsOutR (And a b) ++ [flattenOrTree (Or c d)]
    operatorsOutR (And (Leaf a) (And b c)) = [[LiteralAtomicSentence a]] ++ operatorsOutR (And b c)
    operatorsOutR (And (Not (Leaf a)) (And b c)) = [[LiteralNegationAtomicSentence a]] ++ operatorsOutR (And b c)
    operatorsOutR (And (Or a b) (And c d))  = [flattenOrTree (Or a b)] ++ operatorsOutR (And c d)
    operatorsOutR (Not (Leaf a)) = [[LiteralNegationAtomicSentence a]]
    operatorsOutR (Leaf a) = [[LiteralAtomicSentence a]]

    flattenOrTree (Or (Leaf a) (Leaf b)) = [LiteralAtomicSentence a, LiteralAtomicSentence b]
    flattenOrTree (Or (Not (Leaf a)) (Leaf b)) = [LiteralNegationAtomicSentence a, LiteralAtomicSentence b]
    flattenOrTree (Or (Leaf a) (Not (Leaf b))) = [LiteralAtomicSentence a, LiteralNegationAtomicSentence b]
    flattenOrTree (Or (Not (Leaf a)) (Not (Leaf b))) = [LiteralNegationAtomicSentence a, LiteralNegationAtomicSentence b]
    flattenOrTree (Or (Leaf a) (Or b c)) = [LiteralAtomicSentence a] ++ flattenOrTree (Or b c)
    flattenOrTree (Or (Not (Leaf a)) (Or b c)) = [LiteralNegationAtomicSentence a] ++ flattenOrTree (Or b c)
    flattenOrTree (Or (Or a b) (Leaf c)) = flattenOrTree (Or a b) ++ [LiteralAtomicSentence c]
    flattenOrTree (Or (Or a b) (Not (Leaf c))) = flattenOrTree (Or a b) ++ [LiteralNegationAtomicSentence c]
    flattenOrTree (Or (Or a b) (Or c d)) = flattenOrTree (Or a b) ++ flattenOrTree (Or c d)

convertToClausalForm :: LogicTree -> [Clause]
convertToClausalForm = operatorsOut . distribution . removeDoubleNegations . negationsIn . removeDoubleNegations . implicationsOut

main :: IO ()
main = do
    let exampleTree = Not (And (Leaf "g") (Implies (Leaf "r") (Leaf "f"))) :: LogicTree -- ¬g ∧ (r ⇒ f)
    -- let exampleTree = Implies (Leaf "m") (Or (Leaf "p") (Leaf "q"))
    -- let exampleTree = And (Leaf "g") (Implies (Leaf "r") (Leaf "f")) -- g ∧ (r ⇒ f)
    -- let exampleTree = And (Leaf "g") (Not (Not (Leaf "r")))
    putStrLn . show $ convertToClausalForm exampleTree
