

type pkey, skey, tag, message.
op keys : (pkey * skey) distr.


require BLT.
clone import BLT.BLT_Scheme_Theory as B with type pkey <- pkey,
                                             type skey <- skey,
                                             type tag  <- tag,
                                             type message <- message,
                                             type RI      <- (message * tag),
                                             op   keys <- keys,
                                             op   toRI <- fun x, x.                                          
export B.
