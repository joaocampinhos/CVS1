datatype ENTRY = PACK(key:int, val:int);
datatype RES = NONE | SOME(int);

class DICT {

  var d:array<ENTRY>;
  var elems:int;
  var tsize:int;

  constructor (size:int)
  modifies this, d;
  requires size > 0;
  {
    d := new ENTRY[size];
    elems := 0;
    tsize := size;
  }

  method assoc(k:int, v:int)
  modifies this, d;
  requires d != null && d.Length > elems;
  {
    var x:RES := find(k);
    if (x == NONE) {
      d[elems] := PACK(k, v);
      elems := elems + 1;
    }
    else {
      //chave repetida
      //TODO: saber como tratar isto
    }
  }

  method find(k:int) returns (r:RES)
  requires d != null && d.Length > elems;
  {
    var i:int := 0;
    while (i < elems) {
      if (d[i].key == k) {
        return SOME(d[i].val);
      }
      i := i + 1;
    }
    return NONE;
  }

  method delete(k:int)
  {
    var x:RES := find(k);
    if (x == NONE) {
      //Não existe, não apaga
    }
    else {
      //Existe! dá um shift no array
      //se o find desse o indice, em javascript era assim:
      //array.splice(find(k), 1);
      //Mas em java, temos de criar um array temporario e copiar tudo menos o que apagamos. É muito lindo!
    }
  }

}


class test {
  method main() {

    //ENTÃO ESTA MERDA DIZ QUE PODE DAR ERRO!! AI O CRL!!!
    var t:DICT := new DICT(10);

  }
}
