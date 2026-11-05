module

public import VerifiedGarbage.Impl.Rsa.X86_64.WordValidation
public import VerifiedGarbage.Proof.Rsa.X86_64.WordFast
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import VerifiedGarbage.Proof.Framework.Offset

-- separate module: isolate workspace-address and framing lemmas from instruction execution

/-! # Views of the CRT validation reducer's second workspace -/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.WordValidation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- The second workspace begins beyond the original eight arrays. -/
def start (w : Nat) : Nat := slot w 8

def span (w : Nat) : Nat := slot w 17

theorem word_view (m : Mem) (B : Addr) (a d : Nat) : word m (off B a) d = word m B (a + d) := by
  simp only [Bignum.word, off, BitVec.add_assoc, BitVec.ofNat_add]

theorem wv_view (m : Mem) (B : Addr) (a d n : Nat) : wv m (off B a) d n = wv m B (a + d) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [wv, wv, ih, word_view, show a + (d + 8 * n) = a + d + 8 * n by omega_arith]

/-- An address outside a subrange is outside that range's rebased view. -/
theorem ofs_view_out {B x : Addr} {a n : Nat} (h : a + n ≤ 2 ^ 64) (hn : 0 < n)
    (hx : ofs B x < a ∨ a + n ≤ ofs B x) : n ≤ ofs (off B a) x := by
  have ha : a < 2 ^ 64 := by omega_using [h, hn]
  have hxlt : ofs B x < 2 ^ 64 := (x - B).isLt
  change n ≤ (x - (B + BitVec.ofNat 64 a)).toNat
  rw [← BitVec.sub_sub, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]
  change n ≤ (2 ^ 64 - a + ofs B x) % 2 ^ 64
  omega_using [h, hx, hxlt, ha]

/-- Writes confined to the second workspace leave all other original bytes alone. -/
theorem outside_view {B : Addr} {a n : Nat} {m m' : Mem} (h : a + n ≤ 2 ^ 64) (hn : 0 < n)
    (hf : InScr (off B a) n m m') : Outside B a n m m' :=
  fun x hx => hf x (ofs_view_out h hn hx)

/-- Restoring `rdi` recovers the usual arithmetic register frame. -/
theorem restore_base {s t : State} (hk : Keep (.rdi :: mmRegs) s t) (hd : t.gpr .rdi = s.gpr .rdi) :
    Keep mmRegs s t := by
  refine ⟨?_, hk.2⟩
  intro r hr
  by_cases hrd : r = .rdi
  · subst hrd; exact hd
  · exact hk.gpr (by simp only [List.mem_cons, not_or]; exact ⟨hrd, hr⟩)

end VG.Proof.Rsa.X86_64.WordValidation
