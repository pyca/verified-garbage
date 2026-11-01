module

public import VerifiedGarbage.Impl.Dsa.X86.Pow
public import VerifiedGarbage.Impl.Dsa.X86.CombSetup
public import VerifiedGarbage.Impl.Mont.X86.CombPower
public import VerifiedGarbage.Impl.Dsa.HelperLayout

/-! Per-call DSA comb storage and callable helpers. The table algorithms and
Montgomery arithmetic are shared; only the keygen scratch placement is DSA-specific. -/

@[expose] public section
namespace VG.Impl.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic

/-- Disjoint from the arithmetic workspace, packed domain and sampled scalar. -/
def context (n : Nat) : Nat := if n == 16 then 9216 else 16384

def layout (n e : Nat) : Impl.Dsa.FixedBaseComb.Layout :=
  { Pow.layout n e with context := context n, size := context n + 34*8*n }

def core (prepare : Bool) (n e : Nat) : Prog isa :=
  .seq (if prepare then .seq (setup n) (Mont.X86.Comb.combBuild n e (context n))
    else contextStart n)
    (Mont.X86.Comb.combPower n e (context n) prepare)

def body (prepare : Bool) (n e : Nat) : Prog isa :=
  .seq (.block Pow.save) (.seq (core prepare n e) (.block Pow.restore))

def name (prepare : Bool) (n e : Nat) : String :=
  if prepare then s!"vg_dsa_comb_prepare_{(layout n e).n}_{(layout n e).e}"
  else s!"vg_dsa_comb_pow_{(layout n e).n}_{(layout n e).e}"

def call (prepare : Bool) (n e : Nat) : Prog isa :=
  .seq (.block [.mov .eax (.imm (BitVec.ofNat 32 ((layout n e).size / 8)))])
    (.frame (.push [.eax, .edi]) (.call (name prepare n e) (body prepare n e)) (.pop .eax 2))

end VG.Impl.Dsa.X86.Comb
