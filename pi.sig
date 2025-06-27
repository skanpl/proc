-- the types
chan : Type
proc : Type
lab: Type


-- the constructors for proc
Zero : proc  
Par : proc -> proc -> proc 
Rcv : chan -> (bind chan in proc) -> proc
Send : chan -> chan -> proc -> proc
Nu : (bind chan in proc) -> proc


-- constructors for lab
Lsend : chan -> chan -> lab 
Lrcv : chan -> chan -> lab
LbdSend : chan -> lab
Ltau : lab



