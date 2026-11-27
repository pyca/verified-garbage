module

/-!
# The AES S-box as a Boolean circuit

Gates on numbered variables, and the S-box as a list of them: 112 gates, 32
of them ANDs. Applied to words bit by bit, it computes as many S-boxes as a
word has bits.

The S-box is an inversion in GF(2⁸) between linear maps. As Boyar and Peralta
do ("A New Combinational Logic Minimization Technique with Applications to
Cryptology", SEA 2010), GF(2⁸) is built as a tower over GF(2⁴) and GF(2²): a
linear map of the input gives the operands of nine ANDs, whose sums give the
norm, an element of GF(2⁴), inverted by the circuit of their Figure 2 (5
ANDs); eighteen more ANDs and a linear map give the output. The bases of the
tower were found by enumerating them, and the two linear maps' programs by
the paper's distance heuristic with ties broken at random, for the fewest
gates. The constant `{63}` is added by `xnor`s.

Each target's proof checks the code made from the circuit on all 256 inputs;
nothing here needs to be trusted.
-/

@[expose] public section

namespace VG.Impl.Aes.Circuit

inductive Op
  | xor | and | xnor
  deriving DecidableEq, Repr

/-- `dst := op a b`, on variables. -/
structure Gate where
  dst : Nat
  op : Op
  a : Nat
  b : Nat
  deriving DecidableEq, Repr

def xor (d a b : Nat) : Gate := ⟨d, .xor, a, b⟩
def and (d a b : Nat) : Gate := ⟨d, .and, a, b⟩
def xnor (d a b : Nat) : Gate := ⟨d, .xnor, a, b⟩

/-- The input's bit `i` (bit 0 the least significant), and the output's. -/
def x (i : Nat) : Nat := i
def s (i : Nat) : Nat := 200 + i

/-! ## What is left of a circuit, for register allocation -/

/-- The gates from some point on. -/
structure Rest where
  gates : List Gate

namespace Rest

def ofGates (gs : List Gate) : Rest := ⟨gs⟩

def tail (r : Rest) : Rest := ⟨r.gates.tail⟩

def usesVar (v : Nat) (g : Gate) : Bool := g.a == v || g.b == v

/-- Whether a gate reads the variable. -/
def reads (r : Rest) (v : Nat) : Bool := r.gates.any (usesVar v)

/-- How many gates until one reads the variable (all of them, if none does). -/
def nextUse (r : Rest) (v : Nat) : Nat := r.gates.findIdx (usesVar v)

end Rest

/-- The S-box, from the bits `x i` to the bits `s i`. -/
def sbox : List Gate := [
  ⟨8, .xor, 5, 2⟩, ⟨9, .xor, 8, 1⟩, ⟨10, .xor, 9, 6⟩, ⟨11, .xor, 9, 0⟩, ⟨12, .xor, 10, 3⟩,
  ⟨13, .xor, 12, 7⟩, ⟨14, .xor, 13, 8⟩, ⟨15, .xor, 14, 11⟩, ⟨16, .xor, 15, 5⟩, ⟨17, .xor, 11, 7⟩,
  ⟨18, .xor, 15, 4⟩, ⟨19, .xor, 15, 10⟩, ⟨20, .xor, 16, 7⟩, ⟨21, .xor, 18, 20⟩,
  ⟨22, .and, 18, 15⟩, ⟨23, .xor, 14, 4⟩, ⟨24, .xor, 13, 4⟩, ⟨25, .xor, 18, 13⟩,
  ⟨26, .and, 20, 10⟩, ⟨27, .and, 23, 25⟩, ⟨28, .xor, 23, 1⟩, ⟨29, .xor, 27, 26⟩,
  ⟨30, .and, 21, 19⟩, ⟨31, .xor, 27, 30⟩, ⟨32, .xor, 19, 28⟩, ⟨33, .xor, 23, 16⟩,
  ⟨34, .and, 17, 28⟩, ⟨35, .and, 33, 32⟩, ⟨36, .xor, 31, 34⟩, ⟨37, .xor, 31, 35⟩,
  ⟨38, .and, 11, 24⟩, ⟨39, .and, 7, 9⟩, ⟨40, .xor, 36, 22⟩, ⟨41, .xor, 37, 38⟩,
  ⟨42, .xor, 22, 39⟩, ⟨43, .xor, 29, 38⟩, ⟨44, .xor, 20, 6⟩, ⟨45, .xor, 40, 8⟩,
  ⟨46, .xor, 42, 29⟩, ⟨47, .and, 16, 6⟩, ⟨48, .xor, 46, 44⟩, ⟨49, .xor, 43, 47⟩,
  ⟨50, .xor, 16, 9⟩, ⟨51, .xor, 49, 50⟩, ⟨52, .xor, 41, 14⟩, ⟨53, .xor, 45, 52⟩,
  ⟨54, .and, 48, 45⟩, ⟨55, .xor, 52, 54⟩, ⟨56, .xor, 51, 54⟩, ⟨57, .and, 56, 53⟩,
  ⟨58, .xor, 48, 51⟩, ⟨59, .xor, 52, 57⟩, ⟨60, .xor, 45, 59⟩, ⟨61, .and, 59, 7⟩,
  ⟨62, .xor, 55, 59⟩, ⟨63, .and, 52, 62⟩, ⟨64, .xor, 63, 60⟩, ⟨65, .and, 64, 20⟩,
  ⟨66, .xor, 55, 63⟩, ⟨67, .and, 58, 55⟩, ⟨68, .xor, 51, 67⟩, ⟨69, .and, 64, 10⟩,
  ⟨70, .and, 68, 66⟩, ⟨71, .xor, 70, 58⟩, ⟨72, .xor, 68, 71⟩, ⟨73, .and, 72, 33⟩,
  ⟨74, .xor, 68, 59⟩, ⟨75, .and, 74, 24⟩, ⟨76, .and, 72, 32⟩, ⟨77, .and, 71, 21⟩,
  ⟨78, .and, 74, 11⟩, ⟨79, .xor, 78, 73⟩, ⟨80, .and, 71, 19⟩, ⟨81, .xor, 71, 64⟩,
  ⟨82, .xor, 74, 81⟩, ⟨83, .xor, 61, 73⟩, ⟨84, .xor, 59, 64⟩, ⟨85, .and, 59, 9⟩,
  ⟨86, .xor, 76, 80⟩, ⟨87, .xor, 86, 75⟩, ⟨88, .and, 82, 25⟩, ⟨89, .xor, 86, 88⟩,
  ⟨90, .xor, 89, 85⟩, ⟨91, .xor, 69, 85⟩, ⟨92, .and, 84, 6⟩, ⟨93, .and, 84, 16⟩,
  ⟨94, .xor, 90, 92⟩, ⟨95, .and, 82, 23⟩, ⟨96, .and, 68, 28⟩, ⟨97, .xor, 95, 77⟩,
  ⟨98, .xor, 80, 96⟩, ⟨99, .and, 81, 18⟩, ⟨100, .and, 68, 17⟩, ⟨101, .xor, 97, 99⟩,
  ⟨102, .xor, 98, 91⟩, ⟨103, .xor, 83, 101⟩, ⟨201, .xnor, 101, 100⟩, ⟨104, .and, 81, 15⟩,
  ⟨202, .xor, 103, 93⟩, ⟨203, .xor, 94, 104⟩, ⟨105, .xor, 79, 97⟩, ⟨200, .xnor, 105, 102⟩,
  ⟨205, .xor, 102, 201⟩, ⟨106, .xnor, 201, 88⟩, ⟨107, .xor, 106, 91⟩, ⟨108, .xor, 106, 202⟩,
  ⟨109, .xnor, 200, 100⟩, ⟨110, .xor, 109, 65⟩, ⟨206, .xnor, 108, 87⟩, ⟨207, .xor, 107, 104⟩,
  ⟨111, .xor, 110, 77⟩, ⟨204, .xor, 111, 61⟩]

end VG.Impl.Aes.Circuit
