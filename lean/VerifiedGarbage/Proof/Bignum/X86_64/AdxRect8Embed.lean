import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8Step
import VerifiedGarbage.Proof.Bignum.Rectangular

/-! Embed a local tile update in the full raw product without subtraction. -/
namespace VG.Proof.Bignum.X86_64.AdxRect8
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64

/-- Unchanged words before and after the tile cancel from the value equation. -/
theorem embed {m m' : Mem} {B : Addr} {e d n : Nat} {extra : List (Nat × Nat)}
    (hn : d+16 ≤ n) (hZ : e+8*n ≤ (2 : Nat)^64) (hc : ∀ r ∈ extra, r.1+r.2 ≤ e)
    (hf : Frm B ((e+8*d,128)::extra) m m') :
    wv m' B e n + (2 : Nat)^(64*d)*wv m B (e+8*d) 16 =
      wv m B e n + (2 : Nat)^(64*d)*wv m' B (e+8*d) 16 := by
  have lo : wv m' B e d = wv m B e d := hf.wv_eq (by
    intro r hr
    simp only [List.mem_cons] at hr
    rcases hr with rfl | hr
    · simp only []; omega
    · have := hc r hr; omega) (by omega)
  have hi : wv m' B (e+8*(d+16)) (n-(d+16)) = wv m B (e+8*(d+16)) (n-(d+16)) :=
    hf.wv_eq (by
      intro r hr
      simp only [List.mem_cons] at hr
      rcases hr with rfl | hr
      · simp only []; omega
      · have := hc r hr; omega) (by omega)
  have shape : n = d+(16+(n-(d+16))) := by omega
  rw [shape,wv_add,wv_add,wv_add,wv_add]
  rw [show e+8*d+8*16 = e+8*(d+16) by omega,lo,hi]
  simp only [show 64*16=1024 from rfl]
  generalize (2 : Nat)^1024 = Q
  exact (VG.Proof.Bignum.Rectangular.surround (A := wv m B e d) (P := (2 : Nat)^(64*d))
    (X := wv m B (e+8*d) 16) (X' := wv m' B (e+8*d) 16)
    (Q := Q) (Y := wv m B (e+8*(d+16)) (n-(d+16))))

/-- A tile's carry equation extends to the whole raw product. -/
theorem embed_value {m m' : Mem} {B : Addr} {e d n u v cin cout q r : Nat} {extra : List (Nat × Nat)}
    (hn : d+16 ≤ n) (hZ : e+8*n ≤ (2 : Nat)^64) (hc : ∀ r ∈ extra, r.1+r.2 ≤ e)
    (hf : Frm B ((e+8*d,128)::extra) m m')
    (ht : wv m' B (e+8*d) 16 + q*cout =
      wv m B (e+8*d) 16 + u*v + r*cin) :
    wv m' B e n + (2 : Nat)^(64*d)*q*cout =
      wv m B e n + (2 : Nat)^(64*d)*(u*v) + (2 : Nat)^(64*d)*r*cin := by
  have eq := embed hn hZ hc hf
  exact VG.Proof.Bignum.Rectangular.lift_value eq ht

end VG.Proof.Bignum.X86_64.AdxRect8
