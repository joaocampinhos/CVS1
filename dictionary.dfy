/**
 * CVS 2015 - 1st + 2nd Handout
 *
 * Authors
 *   João Campinhos  41721
 *   Pedro Durães    41911
 */
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

    // Todas as chaves devem ser únicas
    ( forall i, j :: 0 <= i < elems && 0 <= j < elems && i != j ==> d[i].key != d[j].key )

  }

  constructor()
  modifies this;
  ensures RepInv();
  {

    // Inicia a estrutura que guarda o dicionário
    d := new ENTRY[8];
    elems := 0;

  }

  method assoc(k:int, v:int)
  modifies this, d;
  requires RepInv();
  ensures RepInv();
  // Se o array estiver cheio, então o seu tamanho duplica
  ensures old(elems) == old(d.Length) ==> d.Length == old(d.Length) * 2;
  // Existe a chave k no dicionário e fica tudo na mesma
  ensures old(elems) == elems ==> exists i :: 0 <= i < old(elems) ==> old(d[i].key) == k;
  // Não existe na estrutura a chave k e o número de elementos na nova estrutura é incrementado e já existe na nova estrutura o elemento com a chave k e valor v
  ensures elems == old(elems)+1 ==> forall i :: 0 <= i < old(elems) ==> old(d[i].key) != k && exists j :: 0 <= j < elems ==> d[j].key == k && d[j].val == v;
  {

    // Se o array já estiver cheio, duplica o seu tamanho
    if (elems == d.Length) {
      var b := new ENTRY[2 * d.Length];
      forall (i | 0 <= i < elems) {
        b[i] := d[i];
      }
      d := b;
    }

    var e:int := getIndex(k);

    // Se ainda não existe a chave k no dicionário, adiciona
    if (e == -1) {
      d[elems] := PACK(k, v);
      elems := elems + 1;
    }

  }

  method find(k:int) returns (r:RES)
  requires RepInv();
  ensures RepInv();
  // Existe um elemento no array cuja chave é k (e o r[esultado] é o valor correspondente a essa chave)
  // OU
  // Para todos os elementos no array, não existe nenhum que tenha a chave k (e o r[esultado] é NONE)
  ensures (exists i :: 0 <= i < elems ==> d[i].key == k ==> SOME(d[i].val) == r) || (r == NONE && forall i :: 0 <= i < elems ==> d[i].key != k);
  {

    var e:int := getIndex(k);

    if (e != -1) {
      return SOME(d[e].val);
    }

    return NONE;

  }

  method delete(k:int)
  modifies this, d;
  requires RepInv();
  ensures RepInv();
  // Existe a chave k no dicionário e fica tudo na mesma
  ensures old(elems) == elems ==> forall i :: 0 <= i < old(elems) ==> old(d[i].key) != k;
  // Existe na estrutura a chave k e o número de elementos na nova estrutura é decrementado e já não existe na nova estrutura o elemento com a chave k
  ensures (elems == old(elems)-1) ==> (exists i :: 0 <= i < old(elems) ==> old(d[i].key) == k && forall j :: 0 <= j < elems ==> d[j].key != k);
  {

    var e:int := getIndex(k);

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


  // Métodos auxiliares
  //--------------------

  // Verifica se a chave existe no dicionário e retorna o seu índice
  method getIndex(k:int) returns(e:int)
  requires RepInv();
  ensures RepInv();
  // O resultado é -1, logo todas as chaves do array são diferentes de k
  ensures e == -1 ==> (forall j :: 0 <= j < elems ==> d[j].key != k);
  // O resultado é -1, logo esse resultado está dentro dos limites do array e a chave do elemento nesse indice é igual a k
  ensures e != -1 ==> 0 <= e < elems && d[e].key == k;
  {

    var i:int := 0;
    e := -1;

    while (i < elems)
    invariant 0 <= i <= elems;
    invariant e == -1 ==> forall j :: 0 <= j < i ==> d[j].key != k;
    invariant e != -1 ==> 0 <= e < i && d[e].key == k;
    {
      if (d[i].key == k) {
        e := i;
        break;
      }
      i := i + 1;
    }

  }

}
