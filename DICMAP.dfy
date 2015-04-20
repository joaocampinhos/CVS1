datatype ENTRY = PACK(key:int, val:int);
datatype RES = NONE | SOME(int);

class DICT {

  var m:map<int, ENTRY>;

  constructor ()
  {

  }

  method assoc(k:int, v:int)
  modifies this;
  {
    m := m[k := PACK(k,v)];
  }

  method find(k:int) returns (r:RES)
  {
    return NONE;
  }

  method delete(k:int)
  modifies this;
  {
    m := map i | i in m && i != k :: m[i];
  }

}
