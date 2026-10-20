module

public import VerifiedGarbage.Proof.Ecdsa.X86_64.SlotOps
import VerifiedGarbage.Proof.Weierstrass.X86_64.Unch
import VerifiedGarbage.Proof.Mont.X86_64.Ops

/-! # Shared arithmetic in ECDSA's outer phases -/

@[expose] public section
namespace VG.Proof.Ecdsa.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64
open VG.Impl.Ecdsa.X86_64 VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64
open VG.Proof.Weierstrass

variable {c : Cfg}

theorem sharedMod_ok {M : Mod} {m : Nat} {mem : Mem} {base : Addr}
    (hM : ModOkW M size m mem base) (hMn : M.n = c.n) {jm : Nat}
    (hMo : M.mo = c.sl jm) (hj : jm < 45) :
    ModOkW (c.sharedMod M m) size m mem base := by
  refine ⟨hM.n0, hM.mo, ?_, ?_, hM.val, hM.inv, ?_⟩
  · change (if c.n = 8 then c.sl 62 else M.tmp) + 8 * M.n ≤ size
    split
    · rename_i h8
      rw [hMn, sl_eq c 62, h8]
      decide
    · exact hM.tmp
  · change M.mo + 8 * M.n ≤ (if c.n = 8 then c.sl 62 else M.tmp) ∨
      (if c.n = 8 then c.sl 62 else M.tmp) + 8 * M.n ≤ M.mo
    split
    · rw [hMn, hMo]; exact sl_apart c (by omega)
    · exact hM.sep
  · have h := hM.red
    simp only [Mod.ok, Bool.and_eq_true] at h
    simp only [Cfg.sharedMod, Mod.ok, Option.all_some, beq_self_eq_true,
      Bool.and_true, Bool.and_eq_true]
    exact ⟨⟨⟨h.1.1.1.1, h.1.1.2⟩, h.1.2⟩, h.2⟩

theorem sv_shared_keep {M : Mod} {m : Nat} (hMn : M.n = c.n) (hMt : M.tmp = c.sl TMP)
    (h7 : c.n < 10) {base : Addr} (hn : base.toNat + size ≤ 2 ^ 64)
    {o : Nat} {s s' : State} (h : OpKeep (c.sharedMod M m) base (c.sl o) s s')
    {i : Nat} (hi : i < 45) (hio : i ≠ o) (hit : i ≠ TMP) :
    sv c base s' i = sv c base s i := by
  have hl := sl_le c h7 hi
  refine h.unch.wordsVal (fun w hw => ?_) (by omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · change c.sl i + 8 * c.n ≤ c.sl o ∨ c.sl o + 8 * M.n ≤ c.sl i
    rw [hMn]; exact sl_apart c hio
  · simp only [Cfg.sharedMod, hMn, hMt]
    split
    · exact sl_apart c (by omega)
    · exact sl_apart c hit

theorem _root_.VG.Proof.Mont.ModOkW.keepShared {M M' : Mod} {m m' : Nat}
    {base : Addr} {s s' : State} (hM : ModOkW M size m s.mem base)
    {j : Nat} (hj : j < 45) (hmo : M.mo = c.sl j) (hMn : M.n = c.n)
    (hM'n : M'.n = c.n) (hM't : M'.tmp = c.sl TMP) (h7 : c.n < 10)
    (hn : base.toNat + size ≤ 2 ^ 64) {o : Nat}
    (h : OpKeep (c.sharedMod M' m') base (c.sl o) s s') (hjo : j ≠ o) (hjt : j ≠ TMP) :
    ModOkW M size m s'.mem base :=
  ⟨hM.n0, hM.mo, hM.tmp, hM.sep, by
    have := sv_shared_keep hM'n hM't h7 hn h hj hjo hjt
    simp only [sv] at this
    rw [hmo, hMn, this, ← hMn, ← hmo]; exact hM.val, hM.inv, hM.red⟩

theorem unch_shared_slots {base : Addr} {mem mem' : Mem} {o : Nat} {l : List Nat}
    {M : Mod} {m : Nat} (hMn : M.n = c.n) (hMt : M.tmp = c.sl TMP)
    (h : Unch base [(c.sl o, 8 * (c.sharedMod M m).n),
      ((c.sharedMod M m).tmp, 8 * (c.sharedMod M m).n)] mem mem')
    (ho : o ∈ l) (ht : TMP ∈ l) (hh : 62 ∈ l) :
    Unch base (l.map fun i => (c.sl i, 8 * c.n)) mem mem' :=
  h.mono fun w hw => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Cfg.sharedMod, hMn, hMt] at hw
    rcases hw with rfl | rfl
    · exact List.mem_map_of_mem ho
    · split
      · exact List.mem_map_of_mem hh
      · exact List.mem_map_of_mem ht


/-- Inline fallback with the same scratch layout as the shared call. -/
theorem slMulShared_inline_ok {M : Mod} {m : Nat} (hMn : M.n = c.n)
    (hMt : M.tmp = c.sl TMP) {jm : Nat} (hMo : M.mo = c.sl jm) (hj : jm < 45)
    (h7 : c.n < 10) {base : Addr} {s : State} (hs : Scr s base size)
    (hM : ModOkW M size m s.mem base) {o a b : Nat} (ho : o < 45)
    (ha : a < 45) (hb : b < 45) (hS : SlotsOk o a b jm) (hB : sv c base s b < m) :
    WP isa (.block (mul (c.sharedMod M m) (c.sl o) (c.sl a) (c.sl b))) s fun s' =>
      OpKeep (c.sharedMod M m) base (c.sl o) s s' ∧ sv c base s' o < m ∧
      sv c base s' o * 2 ^ (64 * c.n) % m = sv c base s a * sv c base s b % m := by
  have apart : ∀ i, i < 45 → i ≠ TMP →
      c.sl i + 8 * M.n ≤ (c.sharedMod M m).tmp ∨
        (c.sharedMod M m).tmp + 8 * M.n ≤ c.sl i := by
    intro i hi hit
    simp only [Cfg.sharedMod, hMn, hMt]
    split
    · exact sl_apart c (by omega)
    · exact sl_apart c hit
  have h := mul_ok hs (sharedMod_ok hM hMn hMo hj)
    (o := c.sl o) (a := c.sl a) (b := c.sl b)
    (by change c.sl o + 8 * M.n ≤ size; rw [hMn]; exact sl_le c h7 ho)
    (by change c.sl a + 8 * M.n ≤ size; rw [hMn]; exact sl_le c h7 ha)
    (by change c.sl b + 8 * M.n ≤ size; rw [hMn]; exact sl_le c h7 hb)
    (apart o ho hS.1) (apart a ha hS.2.1) (apart b hb hS.2.2.1)
    (by change c.sl o + 8 * M.n ≤ M.mo ∨ M.mo + 8 * M.n ≤ c.sl o
        rw [hMn, hMo]; exact sl_apart c hS.2.2.2)
    (by change wordsVal s.mem base (c.sl b) M.n < m; rw [hMn]; exact hB)
  simpa only [show (c.sharedMod M m).n = c.n from hMn] using h

theorem slMulNS_ok (h7 : c.n < 10) {base : Addr} {s : State}
    (hs : Scr s base size) (hM : ModOkW c.MN' size c.C.n s.mem base)
    {o a b : Nat} (ho : o < 45) (ha : a < 45) (hb : b < 45)
    (hS : SlotsOk o a b MN) (hB : sv c base s b < c.C.n) :
    WP isa (opProg c.MNS (.mul (c.sl o) (c.sl a) (c.sl b))).inline s fun s' =>
      OpKeep c.MNS base (c.sl o) s s' ∧ sv c base s' o < c.C.n ∧
      sv c base s' o * 2 ^ (64 * c.n) % c.C.n = sv c base s a * sv c base s b % c.C.n :=
  opMulN_ok hs (sharedMod_ok hM rfl rfl (by decide)) rfl rfl
    (sl_le c h7 ho) (sl_le c h7 ha) (sl_le c h7 hb) hB
    (slMulShared_inline_ok rfl rfl rfl (by decide) h7 hs hM ho ha hb hS hB)

theorem slMulPS_ok (h7 : c.n < 10) {base : Addr} {s : State}
    (hs : Scr s base size) (hM : ModOkW c.MP' size c.C.p s.mem base)
    {o a b : Nat} (ho : o < 45) (ha : a < 45) (hb : b < 45)
    (hS : SlotsOk o a b MP) (hB : sv c base s b < c.C.p) :
    WP isa (opProg c.MPS (.mul (c.sl o) (c.sl a) (c.sl b))).inline s fun s' =>
      OpKeep c.MPS base (c.sl o) s s' ∧ sv c base s' o < c.C.p ∧
      sv c base s' o * 2 ^ (64 * c.n) % c.C.p = sv c base s a * sv c base s b % c.C.p :=
  opMulP_ok hs (sharedMod_ok hM rfl rfl (by decide)) rfl
    (sl_le c h7 ho) (sl_le c h7 ha) (sl_le c h7 hb) hB
    (slMulShared_inline_ok rfl rfl rfl (by decide) h7 hs hM ho ha hb hS hB)

theorem slMulPSFinish_ok (h7 : c.n < 10) {base : Addr} {s : State}
    (hs : Scr s base size) (hM : ModOkW c.MP' size c.C.p s.mem base)
    {o a b : Nat} (ho : o < 45) (ha : a < 45) (hb : b < 45)
    (hS : SlotsOk o a b MP) (hB : sv c base s b < c.C.p) :
    WP isa (c.mulPS (c.sl o) (c.sl a) (c.sl b)).inline s fun s' =>
      OpKeep c.MPS base (c.sl o) s s' ∧ sv c base s' o < c.C.p ∧
      sv c base s' o * 2 ^ (64 * c.n) % c.C.p = sv c base s a * sv c base s b % c.C.p := by
  unfold Cfg.mulPS
  split
  · exact slMulPS_ok h7 hs hM ho ha hb hS hB
  · exact slMulShared_inline_ok rfl rfl rfl (by decide) h7 hs hM ho ha hb hS hB

end VG.Proof.Ecdsa.X86_64
