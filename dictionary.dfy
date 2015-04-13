datatype ENTRY = PACK(key:int, val:int);
datatype RES = NONE | SOME(int);

class DICT {

  var d:array<ENTRY>;
  var elems:int;
  var tsize:int;

  //constructor (size:int)
  method init (size:int)
  modifies this;
  requires size > 0;
  {
    d := new ENTRY[size];
    elems := 0;
    tsize := size;
  }

  method test(x:int,y:int)
  modifies this, d;
  {
    d[0] := PACK(x,y);
  }

  /*method assoc(k:int, v:int)
  modifies this, d;
  {
    var x:RES := find(k);
    if (x == NONE) {
      d[elems] := PACK(k, v);
      elems := elems + 1;
    }
    else {
      //chave repetida
    }
  }
  */

  method find(k:int) returns (r:RES){
    return NONE;
  }

  method delete(k:int){}

}
