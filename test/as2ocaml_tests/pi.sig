
-- the types
chan : Type
proc : Type



-- the constructors for proc
Zero : proc  
Par : proc -> proc -> proc 
Rcv : chan -> (bind chan in proc) -> proc
Send : chan -> chan -> proc -> proc
Nu : (bind chan in proc) -> proc