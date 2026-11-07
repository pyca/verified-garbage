module

import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.Open
public import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.Tables
public import VerifiedGarbage.Proof.AesGcm.AArch64.Open
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Seal
import VerifiedGarbage.Proof.AesGcm.AArch64.Fn
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-!
# AES-GCM on AArch64, interleaved: `open`'s code with the interleaved loops (`openRunWithS`)

Untrusted: everything here is checked by Lean. `openRunWithS` is `openRunAS`
then `omBS` (`openRunWithS_split`), which together leave `OpenPost`, as
`openRunWithP` does (`openRunWithS_postX`), for any `tb` that writes the table
of keys.
-/

@[expose] public section

namespace VG.Proof.AesGcm.AArch64.Fast

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64
open VG.Proof.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (ctxH ctxCiph)
open VG.Proof.Gcm.AArch64.Stitch (Gh8Ok)

/-- What `tb` must do, in `open` from `s₀`: write the table of keys of the
context's hash subkey (`Stitch.TblPost`). -/
def TbForO (tb : List Instr) (Ctx W SP D : Addr) (n : Nat) (s₀ : State) : Prop :=
  ∀ u : State, Env Ctx (W + BitVec.ofNat 64 16) W SP u → u.rd = s₀.rd → u.wr = s₀.wr →
    Frame [workR W, ⟨D, n⟩] s₀.mem u.mem → KeyAt (Spec.Gcm.ctxH s₀.mem Ctx) u.mem W →
    WP isa (.block tb) u (Stitch.TblPost W (Spec.Gcm.ctxH s₀.mem Ctx) u)

/-- `openRunWith_postX` for `openRunWithS`, of the ciphertext at `S` (`x6`):
over it (`S = D`), or out of place (`to`) to the text at `D`; if the tag is
wrong, the text holds the ciphertext. -/
theorem openRunWithS_postXT (v : GcmImpl) (cl : Prog isa) (hMK : Proof.Gcm.AArch64.Pmull.MulKey) (gh : Gh8Ok)
    {tb : List Instr} {Ctx W SP Np A D Tg : Addr} {R nl al n tl : Nat} {to : Bool} {S : Addr}
    {s₀ t : State} {ex : List Region} {I : Mem → Prop} (o : OpenIn Ctx W SP Np A D Tg R nl al n tl s₀ t)
    (h12 : nl = 12)
    (h4 : t.gpr .x4 = A) (h5 : t.gpr .x5 = BitVec.ofNat 64 al) (h6 : t.gpr .x6 = S)
    (h7 : t.gpr .x7 = BitVec.ofNat 64 n) (hal : al ≤ 16) (hT₃ : bytesAt t.mem W tl = bytesAt s₀.mem Tg tl)
    (hok : Spec.Gcm.tagLenOk tl = true)
    (hsrc : DataOk (W + BitVec.ofNat 64 16) W t S n)
    (hsW : (⟨S, n⟩ : Region).Disjoint (workR W)) (hm : cond to ((⟨S, n⟩ : Region).Disjoint ⟨D, n⟩) (S = D))
    (hS : bytesAt t.mem S n = bytesAt s₀.mem S n)
    (hexW : ∀ r ∈ ex, (workR W).Disjoint r) (hexD : ∀ r ∈ ex, (⟨D, n⟩ : Region).Disjoint r)
    (hexC : ∀ r ∈ ex, (⟨Ctx, 256⟩ : Region).Disjoint r)
    (hI : ∀ {m m' : Mem}, I m → Frame [workR W, ⟨D, n⟩] m m' → I m')
    (hgh : ∀ (s' : State) {Y Dd S : Addr} {nb : Nat}, GhCall s' (Ctx + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR W) → Region.Sub ⟨S, 256⟩ (workR W) →
      s'.rd = s₀.rd → s'.wr = s₀.wr → s'.sp = SP → Frame [workR W, ⟨D, n⟩] s₀.mem s'.mem →
      Region.Sub ⟨Dd, 16 * nb⟩ (⟨D, n⟩ : Region) →
      WP isa cl s' fun u => GhPost s' (Ctx + BitVec.ofNat 64 240) Y Dd S nb u ex ∧ I u.mem)
    (htb : TbForO tb Ctx W SP D n s₀) :
    WP isa (Impl.AesGcm.AArch64.Stitch.openRunWithS v.callees tb cl to) t fun u =>
      OpenPostG Ctx W SP Np A D Tg R nl al n tl (bytesAt s₀.mem S n)
        (fun m => bytesAt m D n = bytesAt s₀.mem S n) s₀ u ∧ I u.mem := by
  subst h12
  have L := o.lay
  have F₀ : Frame [workR W, ⟨D, n⟩] s₀.mem t.mem :=
    o.fr.sub fun r hr => ⟨_, List.mem_cons_self .., entry16_work W r hr⟩
  obtain ⟨hc₃, hH₃, hN₃, hA₃, -⟩ := o.vals
  refine (openRunWithS_split v.callees cl tb to).symm.wp (WP.seq (WP.mono (openRunASX_ok cl v hMK gh
    o h4 h5 h6 h7 hal hok hsrc hsW hm hexW hexD hexC (fun hi f => hI hi (f.sub fun r hr => ⟨workR W, List.mem_cons_self .., by
      simp only [List.mem_singleton] at hr; subst hr; exact fun _ h => h⟩))
    (fun s' _ _ _ _ hc sY sS hrd hwr hsp hf hd => hgh s' hc sY sS (hrd.trans o.rd₀) (hwr.trans o.wr₀) hsp
      (F₀.trans hf) hd)
    (fun u he hrd hwr hf key => by
      rw [hH₃] at key ⊢
      exact htb u he (hrd.trans o.rd₀) (hwr.trans o.wr₀) (F₀.trans hf) key))
    fun _ ⟨mo, i₇⟩ => WP.mono (omBS_ok L v o.rounds mo) fun s₄ ⟨hpost, f₈⟩ => ?_))
  have I₄ : I s₄.mem := hI i₇ (f₈.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), fun _ h => h⟩
    · exact ⟨_, List.mem_cons_self .., stW (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩)
  obtain ⟨he₄, x0₄, d₄⟩ := hpost
  have F₄ := (mo.frame.mono fun r hr => List.mem_append_left _ hr).trans
    (f₈.mono fun r hr => List.mem_append_right (⟨D, n⟩ :: (fastFrame W ++ ex)) hr)
  refine ⟨⟨he₄, o.sv.frame F₄ fun r hr => ?_, ?_⟩, I₄⟩
  · rcases List.mem_append.mp hr with hr | hr
    · rcases List.mem_cons.mp hr with h | hr
      · subst h
        exact (o.ddW.sub_right (Lay.wSub (by decide))).symm
      rcases List.mem_append.mp hr with hr | hr
      · exact saved_fastFrame W r hr
      · exact (hexW r hr).sub_left (Lay.wSub (by decide))
    · exact saved_crFrame L o.dat r hr
  · have hCs : bytesAt t.mem S (Stitch.pre n) ++
        bytesAt t.mem (S + BitVec.ofNat 64 (Stitch.pre n)) (n - Stitch.pre n) = bytesAt t.mem S n := by
      rw [← bytesAt_add, Nat.add_sub_cancel' (Nat.mul_div_le n 128)]
    rw [hCs] at x0₄ d₄
    rw [hc₃, hH₃, hN₃, hA₃, hS, hT₃] at x0₄ d₄
    rw [Spec.Gcm.openResult, ite_eq_left hok, Spec.Gcm.decryptWith]
    by_cases hc : (Spec.Gcm.fullTag (ctxCiph s₀.mem Ctx R) (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np 12)
        (bytesAt s₀.mem A al) (bytesAt s₀.mem S n)).take tl = bytesAt s₀.mem Tg tl
    · rw [ite_eq_left hc]
      simp only [hc, decide_true, ite_true] at x0₄ d₄
      exact ⟨by rw [x0₄]; rfl, d₄⟩
    · rw [ite_eq_right hc]
      simp only [hc, decide_false, Bool.false_eq_true, ite_false] at x0₄ d₄
      exact ⟨by rw [x0₄]; rfl, d₄⟩

/-- `openRunWith_postX` for `openRunWithS`, in place. -/
theorem openRunWithS_postX (v : GcmImpl) (cl : Prog isa) (hMK : Proof.Gcm.AArch64.Pmull.MulKey) (gh : Gh8Ok)
    {tb : List Instr} {Ctx W SP Np A D Tg : Addr} {R nl al n tl : Nat}
    {s₀ t : State} {ex : List Region} {I : Mem → Prop} (o : OpenIn Ctx W SP Np A D Tg R nl al n tl s₀ t)
    (h12 : nl = 12)
    (h4 : t.gpr .x4 = A) (h5 : t.gpr .x5 = BitVec.ofNat 64 al) (h6 : t.gpr .x6 = D)
    (h7 : t.gpr .x7 = BitVec.ofNat 64 n) (hal : al ≤ 16) (hT₃ : bytesAt t.mem W tl = bytesAt s₀.mem Tg tl)
    (hok : Spec.Gcm.tagLenOk tl = true)
    (hexW : ∀ r ∈ ex, (workR W).Disjoint r) (hexD : ∀ r ∈ ex, (⟨D, n⟩ : Region).Disjoint r)
    (hexC : ∀ r ∈ ex, (⟨Ctx, 256⟩ : Region).Disjoint r)
    (hI : ∀ {m m' : Mem}, I m → Frame [workR W, ⟨D, n⟩] m m' → I m')
    (hgh : ∀ (s' : State) {Y Dd S : Addr} {nb : Nat}, GhCall s' (Ctx + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR W) → Region.Sub ⟨S, 256⟩ (workR W) →
      s'.rd = s₀.rd → s'.wr = s₀.wr → s'.sp = SP → Frame [workR W, ⟨D, n⟩] s₀.mem s'.mem →
      Region.Sub ⟨Dd, 16 * nb⟩ (⟨D, n⟩ : Region) →
      WP isa cl s' fun u => GhPost s' (Ctx + BitVec.ofNat 64 240) Y Dd S nb u ex ∧ I u.mem)
    (htb : TbForO tb Ctx W SP D n s₀) :
    WP isa (Impl.AesGcm.AArch64.Stitch.openRunWithS v.callees tb cl) t fun u =>
      OpenPost Ctx W SP Np A D Tg R nl al n tl s₀ u ∧ I u.mem :=
  openRunWithS_postXT v cl hMK gh (to := false) o h12 h4 h5 h6 h7 hal hT₃ hok o.dat.ok o.ddW rfl
    o.vals.2.2.2.2 hexW hexD hexC hI hgh htb

end VG.Proof.AesGcm.AArch64.Fast
