(*assaf lovton 209844414 assaflovton@campus.technion.ac.il eden dembinsky 212227888 edendem@campus.technion.ac.il*)
datatype 'a seq = Nil | Cons of 'a * (unit-> 'a seq);
local
    fun isDiv x y = if((x mod y)=0) then true else false;
    fun tail Nil = raise Empty|
    tail(Cons(_,xf)) = xf();
    fun head Nil = raise Empty|
    head(Cons(x,_)) = x;
    fun getSubSeq_aux an 1 1 =  [head(an)]|
    getSubSeq_aux an 1 e =    head(an)::(getSubSeq_aux (tail an) 1 (e-1))|
    getSubSeq_aux an s e =  (getSubSeq_aux (tail an) (s-1) (e-1));
    fun getKDivElems_aux an 0 k =  []|
    getKDivElems_aux an n k = if(isDiv (head an) k) then 
    (head an)::(getKDivElems_aux (tail an) (n-1) k)
    else (getKDivElems_aux (tail an) (n) k);
in
    fun arithmeticSeq a1 d = Cons(a1,fn ()=>(arithmeticSeq (a1+d) d));
    fun getSubSeq a1 d s e = getSubSeq_aux (arithmeticSeq a1 d) s e;
    fun getKDivElems a1 d n k = (getKDivElems_aux (arithmeticSeq a1 d) n k);
end;
datatype 'a lazyTree = tNil | tCons of 'a * (unit -> 'a lazyTree) * (unit -> 'a lazyTree);
local 
fun getValue tNil = raise Empty|
    getValue (tCons(k,_,_)) = k;
fun goLeft tNil = raise Empty|
    goLeft (tCons(_,L,_)) = L();
fun goRight tNil = raise Empty|
    goRight (tCons(_,_,R)) = R();

in
    fun lazyTreeFrom k = tCons (k,fn()=>(lazyTreeFrom (2*k)),fn()=>(lazyTreeFrom (2*k+1)));
    fun  lazyTreeMap (f,tNil)=tNil|
    lazyTreeMap (f,t) = tCons(f (getValue t), fn()=>lazyTreeMap (f,goLeft t),fn()=>lazyTreeMap (f,goRight t));
    fun lazyTreeFilter (f,tNil) = tNil|
    lazyTreeFilter (f,t) = if(f (getValue t)) then 
    tCons(getValue t, fn()=>lazyTreeFilter (f,goLeft t),fn()=>lazyTreeFilter (f,goRight t))
    else tNil;
end;
