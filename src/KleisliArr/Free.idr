module KleisliArr.Free

import Control.Catchable
import Control.IOExcept
import KleisliArr.Basic

%access public export
%default partial

-- IFree.Do is not strictly positive

data IFree : ((i -> Type) -> i -> Type) -> (i -> Type) -> i -> Type where
  Ret : p i -> IFree f p i
  Do : f (IFree f p) i -> IFree f p i

infixr 3 :*

(:*) : ((i -> Type) -> i -> Type) -> (i -> Type) -> i -> Type 
(:*) = IFree

IFunctor f => IFunctor (IFree f) where
  imap     h (Ret pi)     = Ret $ h pi
  imap {t} h (Do {p} fpi) = Do $ imap {s=IFree f p} {t=IFree f t} (imap h) fpi

IFunctor f => IMonad (IFree f) where
  iskip = Ret 
  iextend     h (Ret pi)     = h pi
  iextend {q} h (Do {p} fpi) = Do $ imap {s=IFree f p} {t=IFree f q} (iextend h) fpi

syntax FOpen [p] [k] = Do (InL (R (V p) k))
syntax FGetC [k] = Do (InR (InL (R (V ()) k)))
syntax FClose [k] = Do (InR (InR (R (V ()) k)))

fOpen : FilePath -> (FH :* IState) Closed
fOpen p = FOpen p Ret

fGetC : (FH :* ((Maybe Char) := Open)) Open
fGetC = FGetC Ret 

fClose : (FH :* (() := Closed)) Open
fClose = FClose Ret

runFH : (FH :* (a := Closed)) Closed -> IOExcept FileError a 
runFH (Ret (V a)) = Applicative.pure a
runFH (FOpen s k) = catch
  (IOM (openFile s Read) >>= openFH (k IOpen)) 
  (\_ => runFH (k IClosed))
  where
  openFH : (FH :* (a := Closed)) Open -> File -> IOExcept FileError a
  openFH (FClose k) h = ioe_lift (closeFile h) *> runFH (k $ V ())
  openFH (FGetC k) h = catch
    (do c <- IOM $ fgetc h
        eof <- ioe_lift $ fEOF h
        openFH (k $ V $ if eof then Nothing else Just c) h)
    (\_ => openFH (k $ V Nothing) h)

IFunctor f => IApplicative ((:*) f) where
  pure = ireturn
  mf <*> ms = mf =>= \f => ms =>= \s => ireturn $ f s

readOpenFile : (FH :* (String := Open)) Open
readOpenFile = fGetC =>= 
  maybe [| "" |] (\c => [| (strCons c) readOpenFile |])

fileContents : FilePath -> (FH :* (Maybe String := Closed)) Closed
fileContents p = fOpen p ?>= \b => case b of 
  IClosed => [| Nothing |]
  IOpen => pure Just <*> readOpenFile <* fClose
