
-- the types
chan : Type
proc : Type



-- the constructors for proc
Zero : proc  
Par : proc -> proc -> proc 
Rcv : chan -> (chan -> proc) -> proc
Send : chan -> chan -> proc -> proc
Nu : (chan -> proc) -> proc
