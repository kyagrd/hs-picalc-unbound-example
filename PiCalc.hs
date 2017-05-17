module PiCalc where
import Unbound.LocallyNameless

type Nm = Name Tm
newtype Tm = Var Nm deriving (Eq, Ord, Show)

data Pr  = Null | TauP Pr | Out Tm Tm Pr | In Tm PrB
         | Plus Pr Pr | Par Pr Pr | Nu PrB | Match Tm Tm Pr
         deriving (Eq, Ord, Show)
type PrB = Bind Nm Pr
instance Eq PrB where (==) = aeqBinders
instance Ord PrB where compare = acompare

data Act   = Up Tm Tm  | Tau     deriving (Eq, Ord, Show)
data ActB  = UpB Tm    | DnB Tm  deriving (Eq, Ord, Show)

data Form  = FF | TT | Conj [Form] | Disj [Form]
           | Dia   Act   Form         | Box   Act   Form
           | DiaB  ActB  FormB        | BoxB  ActB  FormB
           | DiaMatch [(Tm,Tm)] Form  | BoxMatch [(Tm,Tm)] Form
           deriving (Eq,Ord,Show)
type FormB = Bind Nm Form
instance Eq FormB where (==) = aeqBinders
instance Ord FormB where compare = acompare

$(derive [''Tm, ''Act, ''ActB, ''Pr, ''Form])

instance Alpha Tm; {-""-}  instance Alpha Act; {-""-} instance Alpha ActB
instance Alpha Pr; {-""-}  instance Alpha Form

instance Subst Tm Tm where isvar (Var x) = Just (SubstName x)
instance Subst Tm Act; {-""-} instance Subst Tm ActB
instance Subst Tm Pr; {-""-} instance Subst Tm Form

infixr 1 .\
(.\) :: Alpha t => Nm -> t -> Bind Nm t
(.\) = bind

x .= y = Match (Var x) (Var y)
inp x = In(Var x)
out x y = Out(Var x)(Var y)
tau = TauP Null
tautau = TauP (TauP Null)

conj  = cnj  . filter (/=TT)  where
                              cnj [] = TT;  cnj  [f] = f; cnj  fs = Conj fs
disj  = dsj  . filter (/=FF)  where                            
                              dsj [] = FF;  dsj  [f] = f; dsj  fs = Disj fs

unbind2' b1 b2 = do  Just (x,p1,_,p2) <- unbind2 b1 b2
                     return (x,p1,p2)
