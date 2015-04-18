datatype ENTRY = PACK(key:int, val:int);
datatype RES = NONE | SOME(int);

class DICT {

  var d:array<ENTRY>; // Array que guarda o dicionário
  var elems:int;      // Número de elementos no array

  function RepInv():bool
  reads this, d;
  {
    // O array nunca pode ser nulo
    (d != null) &&

    // O tamanho do array deve ser sempre positivo
    (d.Length > 0) &&

    // O número de elementos no array não pode ser superior ao seu tamanho
    (elems <= d.Length) &&

    // O número de elementos no array não pode ser negativo
    (elems >= 0) &&

    //Todas as chaves devem ser únicas
    (forall i, j :: 0 <= i < elems && 0 <= j < elems ==> d[i].key != d[j].key)


  }

  constructor ()
  modifies this;
  ensures fresh(d);
  ensures RepInv();
  {

    d := new ENTRY[8];
    elems := 0;

  }

  method assoc(k:int, v:int)
  modifies this, d;
  requires RepInv();
  ensures RepInv();
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
  requires RepInv();
  ensures RepInv();
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
  requires RepInv();
  ensures RepInv();
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
