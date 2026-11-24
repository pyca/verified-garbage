module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Contiguous.Remainder
public import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Run
import VerifiedGarbage.Proof.AesGcm.AArch64.Cmp
import VerifiedGarbage.Proof.Gcm.Compose
import VerifiedGarbage.Proof.AesGcm.AArch64.Loops
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! Authenticate the partial ciphertext block and lengths for either layout.
The wide final load may reach into the already encrypted prefix. Its entire
range lies inside the destination, even when the unstitched suffix is short. -/

@[expose] public section
namespace VG.Proof.AesGcm.AArch64.Contiguous.Prepared

open VG VG.AArch64 VG.Impl.AesGcm.AArch64 VG.WriteBytes
open VG.Impl.Gcm.AArch64.Pmull (Y loadRev)
open VG.Proof.Gcm.AArch64.Pmull
open VG.Spec.Gcm (Block blockAt ofBytes)
open VG.Spec.Aes (bytesAt)
open Fast (KeyAt padStep)

abbrev finishProgram : Prog isa := .seq (.block (Impl.AesGcm.AArch64.Fast.hReload ++ loadRev Y .x20 16 ++
    [mov .x13 .x24,mov .x12 .x23])) Impl.AesGcm.AArch64.Fast.padMulT

theorem finish_ok {wn n j : Nat} {Ctx W SP O : Addr} {s : State} {H : Block}
    (mk : MulKey) (e : Env wn Ctx (word W 16) W SP s)
    (od : DataOk wn (word W 16) W s O n) (key : KeyAt H s.mem W)
    (hj : j ≤ n) (hl : n-j < 16)
    (r23 : s.gpr .x23 = word O j) (r24 : s.gpr .x24 = BitVec.ofNat 64 (n-j))
    (r26 : s.gpr .x26 = BitVec.ofNat 64 n) :
    let y := padStep H (blockAt s.mem (word (word W 16) 16)) (bytesAt s.mem (word O j) (n-j))
    WP isa finishProgram s fun b => b.v Y = ext8 y y ∧ Fast.HKey H b ∧
      Env wn Ctx (word W 16) W SP b ∧ b.gpr .x22 = s.gpr .x22 ∧ b.gpr .x26 = BitVec.ofNat 64 n ∧
      b.gpr .x28 = s.gpr .x28 ∧ Frame [⟨word W 96,16⟩] s.mem b.mem := by
  have lim := e.perm.hWn
  refine WP.seq ((Fast.reloadTail_ok e key r24 r23).mono ?_)
  intro a ⟨ea,ka,ya,x13,x12,ra⟩
  have full := od.of_eq ra.rd ra.wr
  have tail := full.drop hj
  have n26 := (ra.others .x26 (by decide)).trans r26
  refine ((WP.with_rdwr (Fast.padMulT_ok mk ea ka ya x12 x13 (by omega) tail.rd
    (tail.w.sub_right (Lay.wSub (by omega))) n26 od.lt
    (Fast.pad_big full.rd od.lt (by congr 2; omega) hl))).mono ?_)
  intro b ⟨⟨yb,kb,eb,gb,fb,_⟩,_,_⟩
  rw [ra.mem] at fb yb
  exact ⟨yb,kb,eb,(gb _ (by decide)).trans (ra.others _ (by decide)),
    (gb _ (by decide)).trans n26,(gb _ (by decide)).trans (ra.others _ (by decide)),fb⟩

abbrev paddedAad (aad : List Byte) := aad ++ Spec.Gcm.zeros (Spec.Gcm.padLen aad.length)

theorem suffixHash {wn n p j o : Nat} {Ctx St W SP O : Addr} {H : Block} {k : Reg → Addr}
    {m : Mem} {t : State} {aad : List Byte} (L : Lay wn Ctx St W)
    (od : DataOk wn St W t O n) (hp : p ≤ n) (pmod : p%16 = 0) (jmod : j%16 = 0)
    (last : n-p-j < 16)
    (start : blockAt m (word St 16) = Spec.Gcm.ghash H (Spec.Gcm.blocks (paddedAad aad ++ bytesAt m O p)))
    (h : AbsMid wn Ctx St W SP k 16 H (paddedAad aad ++ bytesAt m O p) (word O p) (n-p) o m j t) :
    let q := p+j
    padStep H (blockAt t.mem (word St 16)) (bytesAt t.mem (word O q) (n-q)) =
      Spec.Gcm.ghash H (Spec.Gcm.blocks (Proof.Gcm.padded aad (bytesAt m O n))) := by
  have hj := h.le
  have align : (paddedAad aad ++ bytesAt m O p).length % 16 = 0 := by
    simp only [paddedAad,List.length_append,length_bytesAt,Proof.Gcm.length_zeros]
    have := Proof.Gcm.length_pad_mod aad.length; omega
  have absorbed : Proof.Gcm.Absorbed m (word St 16) (word St 32) H (paddedAad aad ++ bytesAt m O p) := by
    refine ⟨?_,?_⟩
    · rw [Proof.Gcm.whole_of_mod align,List.take_length]; exact start
    · rw [align,Proof.Gcm.whole_of_mod align,List.drop_length]; rfl
  have y := (h.abs absorbed).whole_eq (by simp only [List.length_append,length_bytesAt] at align ⊢; omega)
  rw [List.append_assoc,← bytesAt_add] at y
  have ht : n-(p+j)<16 := by omega
  have eq := bytesAt_frame h.frame (data_absFrame L (.inr rfl) (od.drop (show p+j ≤ n by omega)))
    (show n-(p+j) ≤ 2^64 by have := od.lt; omega)
  dsimp only
  rw [eq,y,← Fast.ghash_padded _ _ _ _ (by rw [length_bytesAt]; omega) (by rw [length_bytesAt]; exact ht),
    ← bytesAt_add,Nat.add_sub_cancel' (show p+j ≤ n by omega)]

end VG.Proof.AesGcm.AArch64.Contiguous.Prepared
