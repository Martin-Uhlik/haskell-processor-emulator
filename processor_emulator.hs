import Data.Maybe ( fromMaybe )

data Memory a = Memory Integer [a] [a] deriving (Show, Eq)

type Value = Integer
data Output = S String | N Value deriving (Show, Eq)
data AddressType = Relative | Absolute deriving (Show, Eq)

data Condition = Neg | Zero | Pos deriving (Show, Eq)

data Instruction = Move RegisterName RegisterName
                 | Assign RegisterName Value
                 | Add RegisterName RegisterName
                 | Negate RegisterName

                 | Load RegisterName
                 | Store RegisterName
                 | Focus AddressType RegisterName

                 | Jump AddressType Integer
                 | JumpIf Condition RegisterName AddressType Integer

                 | Out RegisterName
                 | Trace String

                 | Halt
                 deriving (Show, Eq)


data RegisterName = R1 | R2 | R3 deriving (Show, Eq)
data Registers = Registers Value Value Value deriving (Show, Eq)

type Program = Memory Instruction
type Data = Memory Value


-- ------------------------------------------------------------------------- --
--                                 SOLUTION                                  --
-- ------------------------------------------------------------------------- --

getRegister :: Registers -> RegisterName -> Value
getRegister (Registers x _ _) R1 = x
getRegister (Registers _ x _) R2 = x
getRegister (Registers _ _ x) R3 = x

setRegister :: Registers -> RegisterName -> Value -> Registers
setRegister (Registers _ y z) R1 v = Registers v y z
setRegister (Registers x _ z) R2 v = Registers x v z
setRegister (Registers x y _) R3 v = Registers x y v

fromList :: [a] -> Memory a
fromList x = Memory 0 [] x

fromListInf :: a -> [a] -> Memory a
fromListInf d v = Memory 0 (repeat d) (v ++ (repeat d))

focusRel :: Integer -> Memory a -> Memory a
focusRel 0 m = m
focusRel x (Memory p a []) = if x > 0
    then error "memory index out of range"
    else focusRel (x + 1) (Memory (p - 1) (tail a) (head a : []))
focusRel x (Memory p [] b) = if x < 0
    then error "memory index out of range"
    else focusRel (x - 1) (Memory (p + 1) (head b : []) (tail b))
focusRel x (Memory p a b) = if x > 0
    then focusRel (x - 1) (Memory (p + 1) (head b : a) (tail b))
    else focusRel (x + 1) (Memory (p - 1) (tail a) (head a : b))

focusAbs :: Integer -> Memory a -> Memory a
focusAbs a m@(Memory p _ _) = focusRel (a - p) m

evalStep :: Program -> Data -> Registers -> (Maybe Output, Program, Data, Registers)
evalStep p@(Memory _ _ []) d r = (Nothing, p, d, r)
evalStep p@(Memory _ _ ((Move r1 r2):_)) d r = (Nothing, focusRel 1 p, d, setRegister r r1 (getRegister r r2))
evalStep p@(Memory _ _ ((Assign r1 v):_)) d r = (Nothing, focusRel 1 p, d, setRegister r r1 v)
evalStep p@(Memory _ _ ((Add r1 r2):_)) d r = (Nothing, focusRel 1 p, d, setRegister r r1 (getRegister r r2 + getRegister r r1))
evalStep p@(Memory _ _ ((Negate r1):_)) d r = (Nothing, focusRel 1 p, d, setRegister r r1 (-(getRegister r r1)))

evalStep p@(Memory _ _ ((Load r1):_)) d@(Memory _ _ (a:_)) r = (Nothing, focusRel 1 p, d, setRegister r r1 a)
evalStep p@(Memory _ _ ((Store r1):_)) (Memory i a1 (_:a2)) r = (Nothing, focusRel 1 p, (Memory i a1 ((getRegister r r1):a2)), r)
evalStep p@(Memory _ _ ((Focus a1 r1):_)) d r = if a1 == Relative
    then (Nothing, focusRel 1 p, focusRel (getRegister r r1) d, r)
    else (Nothing, focusRel 1 p, focusAbs (getRegister r r1) d, r)

evalStep p@(Memory _ _ ((Jump a1 i1):_)) d r = jmp a1 i1 p d r
evalStep p@(Memory _ _ ((JumpIf c1 r1 a1 i1):_)) d r = if checkCondition c1 r1 r
    then jmp a1 i1 p d r
    else (Nothing, focusRel 1 p, d, r)

evalStep p@(Memory _ _ ((Out r1):_)) d r = (Just (N (getRegister r r1)), focusRel 1 p, d, r)
evalStep p@(Memory _ _ ((Trace s1):_)) d r = (Just (S s1), focusRel 1 p, d, r)

evalStep p@(Memory _ _ ((Halt):_)) d r = (Nothing, p, d, r)

checkCondition :: Condition -> RegisterName -> Registers -> Bool
checkCondition Neg r1 r = getRegister r r1 < 0
checkCondition Zero r1 r = getRegister r r1 == 0
checkCondition Pos r1 r = getRegister r r1 > 0

jmp :: AddressType -> Integer -> Program -> Data -> Registers -> (Maybe Output, Program, Data, Registers)
jmp a1 i1 p d r = if a1 == Relative
    then (Nothing, focusRel i1 p, d, r)
    else (Nothing, focusAbs i1 p, d, r)

eval :: [Instruction] -> [Value] -> [Output]
eval i v = map (\b -> fromMaybe (N 0) b) (filter (\a -> a /= Nothing) (step (fromList i) (fromListInf 0 v) (Registers 0 0 0)))

step :: Program -> Data -> Registers -> [Maybe Output]
step (Memory _ _ []) _ _ = []
step (Memory _ _ ((Halt):_)) _ _ = []
step p d r = getOutput (evalStep p d r) ++ nextStep (evalStep p d r)
    where
        getOutput (x,_,_,_) = if x == Nothing then [] else [x]
        nextStep (_,p,d,r) = step p d r

