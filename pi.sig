-- Signature for System F

-- the types
chan : Type
proc : Type


-- Res : (bind chan in proc) -> proc
-- the constructors for proc
Zero : proc  
Par : proc -> proc -> proc 
Rcv : chan -> (bind chan in proc) -> proc
Send : chan -> chan -> proc -> proc