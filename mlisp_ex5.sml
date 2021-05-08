(*assaf lovton 209844414 assaflovton@campus.technion.ac.il eden dembinsky 212227888 edendem@campus.technion.ac.il*)
exception MlispError;
local
   fun getS (s,f) = s;
   
   fun isAtom  (ATOM(NIL)) = true | 
        isAtom (ATOM(SYMBOL(x))) = true|
        isAtom (ATOM(NUMBER(x)))= true|
        isAtom (CONS(ATOM(x),ATOM(NIL))) = true|
        isAtom s = false;

    fun atom (ATOM(NIL)) f = ((ATOM(NIL)),f) |
        atom (ATOM(NUMBER(x))) f = ((ATOM(NUMBER(x))),f)|
        atom (ATOM(SYMBOL("nil"))) f = ((ATOM(NIL)),f)|
        atom (ATOM(SYMBOL(x))) f = (((topEnv f) x),f)|
        atom (CONS(ATOM(NUMBER(x)),ATOM(NIL))) f = ((ATOM(NUMBER(x))),f)|
        atom (CONS(ATOM(SYMBOL("nil")),ATOM(NIL))) f = (ATOM(NIL),f)|
        atom (CONS(ATOM(SYMBOL(x)),ATOM(NIL))) f = (((topEnv f) x),f)|
        atom _ _ = raise MlispError;

    fun isPrimitive (CONS(ATOM(SYMBOL("+")),s)) = true|
        isPrimitive (CONS(ATOM(SYMBOL("-")),s)) = true|
        isPrimitive (CONS(ATOM(SYMBOL("*")),s))  = true|
        isPrimitive (CONS(ATOM(SYMBOL("div")),s)) = true|
        isPrimitive (CONS(ATOM(SYMBOL("cons")),s)) = true|
        isPrimitive (CONS(ATOM(SYMBOL("car")),s)) = true|
        isPrimitive (CONS(ATOM(SYMBOL("cdr")),s)) = true|
        isPrimitive (CONS(ATOM(SYMBOL("define")),s)) = true|
        isPrimitive _ = false;

    fun clean (CONS(s,ATOM(NIL))) = if(isPrimitive s) then s else clean s|
    clean s = s;
    
    fun handle_list l f = (pushEnv f (popEnv l));
    
    fun bindActualsFormals_aux (ATOM(NIL)) s f = f|
        bindActualsFormals_aux (CONS(act,xs)) (CONS(ATOM(SYMBOL(form)),ys)) f = (bindActualsFormals_aux xs ys (handle_list f (define form (topEnv f) act )))|
        bindActualsFormals_aux s1 s2 f = f;
        
    fun bindActualsFormals actuals (CONS(formals,xs)) f = (bindActualsFormals_aux actuals formals (pushEnv (topEnv f) f))|
        bindActualsFormals actuals formals f = (bindActualsFormals_aux actuals formals (pushEnv (topEnv f) f));
    
    fun getBody (CONS(actuals,body)) = body|
        getBody s = s;

    fun eva_pri  (CONS(ATOM(SYMBOL("car")),parm1)) f = (eva_pri_aux (CONS(ATOM(SYMBOL("car")),((getS(eval_aux parm1 f))))) f )|
        eva_pri (CONS(ATOM(SYMBOL("cdr")),parm1)) f = (eva_pri_aux (CONS(ATOM(SYMBOL("cdr")),((getS(eval_aux parm1 f))))) f )|
        eva_pri (CONS(ATOM(SYMBOL("define")),(CONS(ATOM(SYMBOL(name)),value)))) f = 
        (eva_pri_aux ((CONS(ATOM(SYMBOL("define")),CONS(ATOM(SYMBOL(name)),value)))) f )|
        eva_pri (CONS(ATOM(SYMBOL(fun_name)),(CONS(parm1,(CONS(parm2,ATOM(NIL))))))) f = 
        (eva_pri_aux ((CONS(ATOM(SYMBOL(fun_name)),(CONS((getS (eval_aux (getS(eval_aux parm1 f)) f)),(CONS((getS (eval_aux (getS(eval_aux parm2 f)) f)),ATOM(NIL)))))))) f )|
        eva_pri s _ = raise MlispError
    
    
    and eva_pri_aux s f = if(isAtom (s)) then (atom (s) f) handle Undefined =>raise MlispError
                       else if (isAtom ( clean s)) then (atom (clean s) f) handle Undefined =>raise MlispError
                       else if(isPrimitive s) then (primitive s f)
                       else if (isPrimitive (clean s)) then (primitive (clean s) f)
                       else raise MlispError
    
    
    and apply (CONS(ATOM(SYMBOL(fun_name)),actuals)) f =
        ((getS(eval_aux (getBody ((topEnv f) fun_name)) (bindActualsFormals actuals ((topEnv f) fun_name) (pushEnv (topEnv f) f))),f))|
        apply s f  = (raise MlispError)
    
    and primitive (CONS(ATOM(SYMBOL("+")),(CONS(ATOM(NUMBER(x)),(CONS(ATOM(NUMBER(y)),ATOM(NIL))))))) f = (ATOM(NUMBER(x+y)),f)|
        primitive (CONS(ATOM(SYMBOL("-")),(CONS(ATOM(NUMBER(x)),(CONS(ATOM(NUMBER(y)),ATOM(NIL))))))) f = (ATOM(NUMBER(x-y)),f)|
        primitive (CONS(ATOM(SYMBOL("*")),(CONS(ATOM(NUMBER(x)),(CONS(ATOM(NUMBER(y)),ATOM(NIL))))))) f = (ATOM(NUMBER(x*y)),f)|
        primitive (CONS(ATOM(SYMBOL("div")),(CONS(ATOM(NUMBER(x)),(CONS(ATOM(NUMBER(y)),ATOM(NIL))))))) f = (ATOM(NUMBER(x div y)),f)|
        primitive (CONS(ATOM(SYMBOL("cons")),(CONS(x,(CONS(y,ATOM(NIL))))))) f = (CONS(x,y),f)|
        primitive (CONS(ATOM(SYMBOL("car")),(CONS(x,y)))) f = (x,f)|
        primitive (CONS(ATOM(SYMBOL("cdr")),(CONS(x,y)))) f = (y,f)|
        primitive (CONS(ATOM(SYMBOL("define")),(CONS(ATOM(SYMBOL(name)),value)))) f = (ATOM(NIL),(handle_list f (define name (topEnv f) value)))|
        primitive _ _ = raise MlispError
    

    and eval_aux s f = if(isAtom (s)) then (atom (s) f) handle Undefined =>raise MlispError
                   else if (isAtom ( clean s)) then (atom (clean s) f) handle Undefined =>raise MlispError
                   else if(isPrimitive s) then (eva_pri s f)
                   else if (isPrimitive (clean s)) then (eva_pri (clean s) f)
                   else (apply s f);

in
    fun eval s f = (eval_aux s f) handle Undefined => raise MlispError;
end;
