datatype ENTRY = PACK(key:int, val:int);
datatype RES = NONE | SOME(int);

class DICT {

  var d:array<ENTRY>; // Array que guarda o dicionário
  var elems:int;      // Número de elementos no array

  constructor ()
  modifies this;
  ensures fresh(d);
  {

    d := new ENTRY[8];
    elems := 0;

  }

  method assoc(k:int, v:int)
  modifies this, d;
  requires d != null && elems <= d.Length && 0 < d.Length && elems >= 0;
  {

    // Se o array já estiver cheio, duplica o seu tamanho
    if (elems == d.Length) {
      var b := new ENTRY[2 * d.Length];
      forall (i | 0 <= i < elems) {
        b[i] := d[i];
      }
      d := b;
    }

    // Pesquisa para saber se já existe a chave
    var x:RES := find(k);
    if (x == NONE) {
      d[elems] := PACK(k, v);
      elems := elems + 1;
    }

  }

  method find(k:int) returns (r:RES)
  requires d != null && elems <= d.Length && 0 < d.Length && elems >= 0;
  {

    var i:int := 0;
    //Itera sobre todo o array à procura da chave
    while (i < elems) {
      if (d[i].key == k) {
        //Se encontrou, retorna o valor pertencente à chave K
        return SOME(d[i].val);
      }
      i := i + 1;
    }
    return NONE;

  }

  method delete(k:int)
  modifies this, d;
  requires d != null && elems <= d.Length && 0 < d.Length && elems >= 0;
  {

    // TODO: passar isto para um método auxiliar (?)
    var i:int := 0;
    var e:int := -1;

    while (i < elems) {
      if (d[i].key == k) {
        e := i;
        break;
      }
      i := i + 1;
    }

    // Se existe a chave, apaga
    if (e != -1) {

        // Decrementamos o elems porque ficamos com menos um elemento
        elems := elems - 1;

        // shift ao array para apagar o elemento
        forall (i | e <= i < elems) {
          d[i] := d[i + 1];
        }
    }

  }

}
