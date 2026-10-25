module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Short.CT
import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Bcast
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Short.CT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Bcast
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec

/-!
# AES-GCM's short path on x86-64: the powers from a prepared context

Untrusted: everything here is checked by Lean. A prepared key context
(`VG.Spec.Gcm.PreparedPowersRepr`) holds `H'¹`–`H'⁴⁸` in pairs, the 64 bytes
at `ctx + 256 + 64 j` being `H'⁴ʲ⁺²`, `H'⁴ʲ⁺¹`, `H'⁴ʲ⁺⁴`, `H'⁴ʲ⁺³`. `powersP`
leaves only the constants (`powersP_run`), and `ghashP` loads each group of
powers from the context, swapped by halves (`vshufi32x4` with `0x4E`), in
the table's order `H'⁴ʲ⁺⁴`–`H'⁴ʲ⁺¹` (`ghLoadP_ok`): it computes what `ghash`
does from the table `tabView` puts at `W + 1536` (`ghashP_ok`), which holds
what `powers` computes (`tabView_ok`): `powOk_powersP`. Both address memory
only from the key context's and `W`'s registers (`powersP_ct`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Short

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.Short
open VG.Proof.AesGcm.X86_64
open VG.Proof.Gcm.X86_64 (revMask blockAt_eq)
open VG.Proof.Gcm.X86_64.Pclmul (Prod prod reduceB Only const_ok ea_at)
open VG.Proof.Gcm.X86_64.StitchZ (lane_ld lane_ld_ok zlane_load)
open VG.Proof.Gcm.X86_64.Stitch (CtxMode zero_xor_b)
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Spec.Gcm (Block ctxH blockAt)

/-! ## The table as `ghashP` sees it -/

/-- `m`, but for the table at `W + 1536`: there, the first eight groups of
the key context's powers, each swapped by halves. -/
def tabView (Ctx W : Addr) (m : Mem) : Mem := fun a =>
  if (a - (W + BitVec.ofNat 64 1536)).toNat < 512 then
    m (Ctx + BitVec.ofNat 64 (256 + 64 * ((a - (W + BitVec.ofNat 64 1536)).toNat / 64) +
      ((a - (W + BitVec.ofNat 64 1536)).toNat % 64 + 32) % 64))
  else m a

theorem read_shift {m m' : Mem} {a b : Addr} {n : Nat}
    (h : ∀ i < n, m (a + BitVec.ofNat 64 i) = m' (b + BitVec.ofNat 64 i)) : m.read a n = m'.read b n := by
  induction n generalizing a b with
  | zero => rfl
  | succ n ih =>
    simp only [Mem.read]
    have h0 := h 0 (by omega_arith)
    simp only [BitVec.add_zero] at h0
    rw [h0, ih fun i hi => ?_]
    have := h (i + 1) (by omega_arith)
    rwa [Offset.add_ofNat_succ, Offset.add_ofNat_succ] at this

/-- Lane `l` of the view's group `j`: lane `(l + 2) % 4` of the context's. -/
theorem tabView_readW (Ctx W : Addr) (m : Mem) {j l : Nat} (hj : j < 8) (hl : l < 4) :
    (tabView Ctx W m).readW (W + BitVec.ofNat 64 1536 + BitVec.ofNat 64 (64 * j + 16 * l)) 128 =
      m.readW (Ctx + BitVec.ofNat 64 (256 + 64 * j + 16 * ((l + 2) % 4))) 128 := by
  simp only [Mem.readW]
  refine congrArg (BitVec.setWidth 128) (read_shift fun i hi => ?_)
  have e : (W + BitVec.ofNat 64 1536 + BitVec.ofNat 64 (64 * j + 16 * l) + BitVec.ofNat 64 i -
      (W + BitVec.ofNat 64 1536)).toNat = 64 * j + 16 * l + i := by
    rw [BitVec.add_assoc (W + _), BitVec.ofNat_add_ofNat, Offset.add_sub_cancel_left, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega_arith)]
  simp only [tabView, e, show 64 * j + 16 * l + i < 512 by omega_arith, ite_true]
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  exact congrArg (fun k => m (Ctx + BitVec.ofNat 64 k)) (by omega_arith)

/-- The view is `m` outside the table. -/
theorem tabView_out (Ctx W : Addr) (m : Mem) : Frame [⟨W + BitVec.ofNat 64 1536, 512⟩] m (tabView Ctx W m) :=
  fun x hx => by
    have h := hx _ (List.mem_singleton_self _)
    simp only [Region.Contains] at h
    simp only [tabView, show ¬ (x - (W + BitVec.ofNat 64 1536)).toNat < 512 by omega_arith, ite_false]

/-- The view of a context disjoint from `W` and the data. -/
theorem tabView_view {Ctx W D : Addr} {n : Nat} (hcw : (⟨Ctx, 1024⟩ : Region).Disjoint ⟨W, 2560⟩)
    (hcd : (⟨Ctx, 1024⟩ : Region).Disjoint ⟨D, n⟩) : TabView (tabView Ctx W) W D n where
  keep f hd j hj l hl := by
    rw [tabView_readW _ _ _ hj hl, tabView_readW _ _ _ hj hl]
    have hs : Region.Sub ⟨Ctx + BitVec.ofNat 64 (256 + 64 * j + 16 * ((l + 2) % 4)), 16⟩ ⟨Ctx, 1024⟩ :=
      Offset.sub_base Ctx (by omega_arith)
    refine f.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    rcases (hd r hr).2 with h | h
    · exact (hcw.sub_left hs).sub_right fun a ha => Region.sub_prefix (by decide) a (h a ha)
    · exact (hcd.sub_left hs).sub_right h
  out := tabView_out Ctx W

/-- With a prepared key context, the view holds what `powers` computes. -/
theorem tabView_ok {m : Mem} {Ctx W : Addr} (hok : Spec.Gcm.PreparedPowersRepr m Ctx) {g : Nat} (hg : g ≤ 8) :
    TabOk (tabView Ctx W m) (W + BitVec.ofNat 64 1536) (ctxH m Ctx) g := fun j hj l hl => by
  rw [tabView_readW _ _ _ (by omega_arith) hl]
  have h2 := hok (2 * j) (by omega_arith)
  have h3 := hok (2 * j + 1) (by omega_arith)
  rcases (by omega_arith : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl | rfl
  · rw [show 256 + 64 * j + 16 * ((0 + 2) % 4) = 256 + 32 * (2 * j + 1) by omega_arith, h3.1,
      show 2 * (2 * j + 1) + 2 = 4 * j + 4 - 0 by omega_arith]; rfl
  · rw [show 256 + 64 * j + 16 * ((1 + 2) % 4) = 272 + 32 * (2 * j + 1) by omega_arith, h3.2,
      show 2 * (2 * j + 1) + 1 = 4 * j + 4 - 1 by omega_arith]; rfl
  · rw [show 256 + 64 * j + 16 * ((2 + 2) % 4) = 256 + 32 * (2 * j) by omega_arith, h2.1,
      show 2 * (2 * j) + 2 = 4 * j + 4 - 2 by omega_arith]; rfl
  · rw [show 256 + 64 * j + 16 * ((3 + 2) % 4) = 272 + 32 * (2 * j) by omega_arith, h2.2,
      show 2 * (2 * j) + 1 = 4 * j + 4 - 3 by omega_arith]; rfl

/-! ## `powersP` -/

/-- `vshufi32x4` with `0x4E`: the two halves swapped. -/
theorem shuf4E (a : Nat → BitVec 128) {l : Nat} (hl : l < 4) : shuf4Lanes a a 0x4E l = a ((l + 2) % 4) := by
  rcases (by omega_arith : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl | rfl <;> rfl

/-- `powersP`: the constants in every lane of `zmm0` and `zmm1`. -/
theorem powersP_run (s : State) :
    WP isa powersP s fun t => t.mem = s.mem ∧
      (∀ l < 4, t.zlane .xmm0 l = revMask) ∧ (∀ l < 4, t.zlane .xmm1 l = poly) ∧
      (∀ r, r ≠ .rax → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  rw [powersP, List.append_assoc, WP.block_append_iff]
  refine WP.mono (const_ok .xmm0 _ s (by decide)) fun s₁ ⟨c₁, o₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (const_ok .xmm1 _ s₁ (by decide)) fun s₂ ⟨c₂, o₂⟩ => ?_
  have O₂ := o₁.trans o₂
  refine WP.mono (pow4c_ok s₂) fun s₃ ⟨b0, b1, f₃⟩ => ⟨by rw [f₃.mem, O₂.mem], fun l hl => ?_,
    fun l hl => ?_, fun r hr => by rw [f₃.gpr, O₂.gpr r hr], by rw [f₃.rd, O₂.rd], by rw [f₃.wr, O₂.wr]⟩
  · rw [b0 l hl, o₂.xmm _ (by decide), c₁, VG.Proof.Gcm.X86_64.Pclmul.rev_eq]
  · rw [b1 l hl, c₂]

/-! ## `ghashP` -/

/-- `ghSetupP`: `rdx` 128 bytes before `G`, `r11` 128 bytes before the
context's powers of `G`'s first group, `r9` the `g` groups, the products
cleared. -/
theorem ghSetupP_ok {Ctx W : Addr} {g : Nat} (s : State) (h13 : s.gpr .r13 = Ctx) (h15 : s.gpr .r15 = W)
    (hmp : s.mem.readW (W + BitVec.ofNat 64 288) 64 = BitVec.ofNat 64 (4 * g)) (hg : g ≤ 8)
    (r288 : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 288) 8) :
    WP isa (.block ghSetupP) s fun t =>
      t.gpr .rdx = W + BitVec.ofNat 64 384 ∧ t.gpr .r9 = BitVec.ofNat 64 g ∧
      t.gpr .r11 = Ctx + BitVec.ofNat 64 (64 + 64 * g) ∧ (∀ l < 4, prod (t.zproj l) = Prod.zero) ∧
      (∀ r, r ≠ .rdx → r ≠ .r9 → r ≠ .r11 → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      ZKeep [.xmm8, .xmm9, .xmm10] s t := by
  rw [show ghSetupP = (ptr .rdx .r15 (gO - 128) ++ [.mov .r9 (.mem (at_ .r15 mpO)), .shift .shr .r9 2,
      .mov .r11 (.reg .r9), .shift .shl .r11 6, .alu .add .r11 (.reg .r13), .alu .add .r11 (imm 64)]) ++
      [.zop (.zbin .vpxord .xmm8 .xmm8 .xmm8), .zop (.zbin .vpxord .xmm9 .xmm9 .xmm9),
       .zop (.zbin .vpxord .xmm10 .xmm10 .xmm10)] from rfl, WP.block_append_iff]
  have e₁ : BitVec.ofNat 64 (4 * g) >>> 2 = BitVec.ofNat 64 g := by rw [shr2 _ (by omega_arith)]; congr 1; omega_arith
  have e₂ : BitVec.ofNat 64 g <<< 6 = BitVec.ofNat 64 (64 * g) := by
    rw [shl_ofNat (by omega_arith)]; congr 1; omega_arith
  apply WP.of_runBlock
  refine ⟨_, by xrun [execShift, h15, hmp, r288, mpO, gO, e₁, e₂], ?_⟩
  refine WP.mono (clear3_ok _) fun t ⟨p, f⟩ => ⟨?_, ?_, ?_, p, fun r h₁ h₂ h₃ => ?_, f.mem, f.rd, f.wr,
    fun r hr l hl => f.zlane r (by simpa using hr) l hl⟩
  · rw [f.gpr]; simp [gpr_setReg, gpr_setFlags, gpr_arithFlags, h15]
  · rw [f.gpr]; simp [gpr_setReg, gpr_setFlags, gpr_arithFlags]
  · rw [f.gpr]; simp [gpr_setReg, gpr_setFlags, gpr_arithFlags, h13]
    rw [BitVec.add_comm (BitVec.ofNat 64 (64 * g)) Ctx, BitVec.add_assoc, ofNat_add_ofNat, Nat.add_comm]
  · rw [f.gpr]; simp [gpr_setReg, gpr_setFlags, gpr_arithFlags, h₁, h₂, h₃]

/-- Four powers from `r11 + 128`, swapped by halves, into `zmm12`, and four
blocks at `rdx + 128` with their products added. -/
theorem ghLoadP_ok (t : State) (h0 : ∀ l < 4, t.zlane .xmm0 l = revMask)
    (hin : InRegions (t.rd ++ t.wr) (t.gpr .rdx + BitVec.ofInt 64 ((128 : Nat) : Int)) 64)
    (hpin : InRegions (t.rd ++ t.wr) (t.gpr .r11 + BitVec.ofInt 64 ((128 : Nat) : Int)) 64) :
    WP isa (.block ghLoadP) t fun t' =>
      (∀ l < 4, prod (t'.zproj l) = (prod (t.zproj l)).acc
        (blockAt t.mem (t.gpr .rdx + BitVec.ofInt 64 ((128 : Nat) : Int) + BitVec.ofNat 64 (16 * l)))
        (t.mem.readW (t.gpr .r11 + BitVec.ofInt 64 ((128 : Nat) : Int) + BitVec.ofNat 64 (16 * ((l + 2) % 4)))
          128)) ∧
      ZFrame [.xmm12, .xmm7, .xmm8, .xmm9, .xmm10, .xmm11] t t' := by
  let ap := t.gpr .r11 + BitVec.ofInt 64 ((128 : Nat) : Int)
  let ad := t.gpr .rdx + BitVec.ofInt 64 ((128 : Nat) : Int)
  let vp := t.mem.readW ap 512
  let t₁ := t.setZ .xmm12 (vp.extractLsb' 0 128) (vp.extractLsb' 128 128) (vp.extractLsb' 256 128)
    (vp.extractLsb' 384 128)
  let t₁' := (ZOp.vshufi32x4 .xmm12 .xmm12 .xmm12 0x4E).exec t₁
  let vd := t₁'.mem.readW ad 512
  let t₂ := t₁'.setZ .xmm7 (vd.extractLsb' 0 128) (vd.extractLsb' 128 128) (vd.extractLsb' 256 128)
    (vd.extractLsb' 384 128)
  rw [show ghLoadP = .vmovdqu32Load .xmm12 (at_ .r11 128) :: .zop (.vshufi32x4 .xmm12 .xmm12 .xmm12 0x4E) ::
      .vmovdqu32Load .xmm7 (at_ .rdx 128) :: VG.Proof.Gcm.X86_64.StitchZ.restZ 2 from rfl, WP.block_cons_iff]
  refine ⟨t₁, by simp only [isa, exec, State.load512, State.ea, at_, hpin, ite_true, Option.map_some]; rfl, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨t₁', rfl, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨t₂, by simp only [isa, exec, State.load512, State.ea, at_, t₁', t₁, ZOp.exec_gpr, ZOp.exec_rd, ZOp.exec_wr,
    ZOp.exec_mem, State.setZ_gpr, State.setZ_rd, State.setZ_wr, State.setZ_mem, hin, ite_true, Option.map_some]; rfl, ?_⟩
  have keep : ∀ r, r ≠ .xmm12 → r ≠ .xmm7 → ∀ l < 4, t₂.zlane r l = t.zlane r l := fun r h12 h7 l hl => by
    simp only [t₂, t₁', t₁]
    rw [State.zlane_setZ_ne _ h7 _ _ _ _ hl, zlane_vshufi32x4 _ _ _ _ _ _ hl]
    simp only [h12, ite_false]
    rw [State.zlane_setZ_ne _ h12 _ _ _ _ hl]
  have l12 : ∀ l < 4, t₂.zlane .xmm12 l = t.mem.readW (ap + BitVec.ofNat 64 (16 * ((l + 2) % 4))) 128 :=
    fun l hl => by
      simp only [t₂]
      rw [State.zlane_setZ_ne _ (by decide) _ _ _ _ hl, zlane_vshufi32x4 _ _ _ _ _ _ hl]
      simp only [ite_true, shuf4E _ hl]
      exact zlane_load t .xmm12 ap (by omega_arith)
  have l7 : ∀ l < 4, t₂.zlane .xmm7 l = t.mem.readW (ad + BitVec.ofNat 64 (16 * l)) 128 := fun l hl =>
    zlane_load t₁' .xmm7 ad hl
  refine WP.mono (WP.zlanes (lane_ld (k := 2) (by decide)) fun l _ => lane_ld_ok (k := 2) (t₂.zproj l))
    fun t' ⟨hk', hq⟩ => ⟨fun l hl => ?_, ?_⟩
  · rw [(hq l hl).1]
    have hp : prod (t₂.zproj l) = prod (t.zproj l) := by
      simp only [prod, State.zproj_xmm, keep .xmm8 (by decide) (by decide) l hl,
        keep .xmm9 (by decide) (by decide) l hl, keep .xmm10 (by decide) (by decide) l hl]
    simp only [hp, State.zproj_xmm, l7 l hl, l12 l hl, keep .xmm0 (by decide) (by decide) l hl, h0 l hl,
      show (2 : Nat) ≠ VG.Impl.Gcm.X86_64.StitchZ.ord 0 by decide, show (2 : Nat) ≠ 0 by decide, ite_false,
      zero_xor_b]
    rw [← blockAt_eq]
  · refine ⟨hk'.gpr, hk'.mem, hk'.rd, hk'.wr, fun r hr l hl => ?_⟩
    have := (hq l hl).2.xmm r (fun h => hr (List.mem_cons_of_mem _ h))
    simp only [State.zproj_xmm] at this
    rw [this, keep r (fun h => hr (h ▸ List.mem_cons_self))
      (fun h => hr (h ▸ List.mem_cons_of_mem _ List.mem_cons_self)) l hl]

/-- A step of the loop: group `j` of `G` times its powers from the
context, added to the products. -/
theorem ghStepP_ok {Ctx W : Addr} {g j : Nat} {m : Mem} (t : State) (hj : j < g) (hg : g ≤ 8)
    (hm : t.mem = m) (h0 : ∀ l < 4, t.zlane .xmm0 l = revMask)
    (hrdx : t.gpr .rdx = W + BitVec.ofNat 64 (384 + 64 * j))
    (hr11 : t.gpr .r11 = Ctx + BitVec.ofNat 64 (64 + 64 * (g - j)))
    (hin : InRegions (t.rd ++ t.wr) (W + BitVec.ofNat 64 (512 + 64 * j)) 64)
    (hpin : InRegions (t.rd ++ t.wr) (Ctx + BitVec.ofNat 64 (192 + 64 * (g - j))) 64)
    (hp : ∀ l < 4, prod (t.zproj l) = gacc (tabView Ctx W m) (W + BitVec.ofNat 64 512) (W + BitVec.ofNat 64 1536) g l j) :
    WP isa (.block ghBodyP) t fun t' =>
      (∀ l < 4, prod (t'.zproj l) =
        gacc (tabView Ctx W m) (W + BitVec.ofNat 64 512) (W + BitVec.ofNat 64 1536) g l (j + 1)) ∧
      t'.gpr .rdx = W + BitVec.ofNat 64 (384 + 64 * (j + 1)) ∧
      t'.gpr .r11 = Ctx + BitVec.ofNat 64 (64 + 64 * (g - (j + 1))) ∧ t'.gpr .r9 = t.gpr .r9 - 1 ∧
      t'.zf = some (t.gpr .r9 - 1 == 0) ∧ (∀ r, r ≠ .rdx → r ≠ .r9 → r ≠ .r11 → t'.gpr r = t.gpr r) ∧
      t'.mem = t.mem ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧
      ZKeep [.xmm12, .xmm7, .xmm8, .xmm9, .xmm10, .xmm11] t t' := by
  have ea₁ : t.gpr .rdx + BitVec.ofInt 64 ((128 : Nat) : Int) = W + BitVec.ofNat 64 (512 + 64 * j) := by
    rw [hrdx, BitVec.ofInt_natCast, add_ofNat_ofNat, show 384 + 64 * j + 128 = 512 + 64 * j by omega_arith]
  have ea₂ : t.gpr .r11 + BitVec.ofInt 64 ((128 : Nat) : Int) = Ctx + BitVec.ofNat 64 (192 + 64 * (g - j)) := by
    rw [hr11, BitVec.ofInt_natCast, add_ofNat_ofNat, show 64 + 64 * (g - j) + 128 = 192 + 64 * (g - j) by omega_arith]
  rw [ghBodyP, WP.block_append_iff]
  refine WP.mono (ghLoadP_ok t h0 (by rw [ea₁]; exact hin) (by rw [ea₂]; exact hpin)) fun t₁ ⟨p₁, f₁⟩ => ?_
  apply WP.of_runBlock
  refine ⟨_, by xrun [], ?_⟩
  refine ⟨fun l hl => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show prod (t₁.zproj l) = _
    rw [p₁ l hl, gacc_succ, ← hp l hl, ea₁, ea₂, add_ofNat_ofNat, add_ofNat_ofNat,
      tabView_readW _ _ _ (by omega_arith) hl, ← hm]
    have hb : blockAt (tabView Ctx W t.mem) (W + BitVec.ofNat 64 512 + BitVec.ofNat 64 (64 * j + 16 * l)) =
        blockAt t.mem (W + BitVec.ofNat 64 (512 + 64 * j + 16 * l)) := by
      rw [add_ofNat_ofNat, show 512 + (64 * j + 16 * l) = 512 + 64 * j + 16 * l by omega_arith, blockAt_eq, blockAt_eq,
        (tabView_out Ctx W t.mem).readW
          (r := ⟨W + BitVec.ofNat 64 (512 + 64 * j + 16 * l), 16⟩) (Region.contains_self _ _) (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact Offset.disjoint W (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)]
    rw [hb, show 192 + 64 * (g - j) + 16 * ((l + 2) % 4) = 256 + 64 * (g - 1 - j) + 16 * ((l + 2) % 4) by omega_arith]
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, ite_true]
    rw [f₁.gpr, hrdx, add_ofNat_ofNat]; congr 1
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, ite_true]
    rw [f₁.gpr, hr11, show 64 + 64 * (g - j) = (64 + 64 * (g - (j + 1))) + 64 by omega_arith, ← add_ofNat_ofNat]
    exact BitVec.add_sub_cancel _ _
  · simp [gpr_setReg, gpr_arithFlags, f₁.gpr]
  · simp [gpr_setReg, gpr_arithFlags, zf_arithFlags, f₁.gpr]
  · intro r h₁ h₂ h₃; simp [gpr_setReg, gpr_arithFlags, h₁, h₂, h₃, f₁.gpr]
  · exact f₁.mem
  · exact f₁.rd
  · exact f₁.wr
  · intro r hr l hl; exact f₁.zlane r hr l hl

/-- `ghashP` computes what `ghash` does from the table `tabView` puts at
`W + 1536`. -/
theorem ghashP_ok {s₀ : State} {Ctx W SP : Addr} (hcov : Covers [⟨Ctx, 1024⟩] (s₀.rd ++ s₀.wr)) :
    GhFrom ghashP (tabView Ctx W) s₀ Ctx W SP := by
  intro g s he hmp hg1 hg h0 h1 hrd hwr
  have wR : ∀ {d n : Nat}, d + n ≤ 2560 → InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 d) n :=
    fun h => in_left (in_off he.perm.w h (by decide))
  have cR : ∀ {d n : Nat}, d + n ≤ 1024 → InRegions (s.rd ++ s.wr) (Ctx + BitVec.ofNat 64 d) n :=
    fun h => by rw [hrd, hwr]; exact in_off hcov h (by decide)
  refine WP.seq (WP.mono (ghSetupP_ok s he.r13 he.r15 hmp hg (wR (by decide)))
    fun s₁ ⟨dx₁, r9₁, r11₁, p₁, g₁, m₁, rd₁, wr₁, z₁⟩ => ?_)
  refine WP.seq (WP.mono (Q := fun (t : State) => (∀ l < 4, prod (t.zproj l) =
      gacc (tabView Ctx W s.mem) (W + BitVec.ofNat 64 512) (W + BitVec.ofNat 64 1536) g l g) ∧
      (∀ r, r ≠ .rdx → r ≠ .r9 → r ≠ .r11 → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      ZKeep [.xmm7, .xmm8, .xmm9, .xmm10, .xmm11, .xmm12] s t) ?_
    fun t ⟨pt, gt, mt, rdt, wrt, zt⟩ => ?_)
  · refine WP.loop (M := isa) (body := .block ghBodyP) (c := .ne)
      (fun (n : Nat) (t : State) => ∃ j, n = g - j ∧ j < g ∧
        t.gpr .rdx = W + BitVec.ofNat 64 (384 + 64 * j) ∧ t.gpr .r11 = Ctx + BitVec.ofNat 64 (64 + 64 * (g - j)) ∧
        t.gpr .r9 = BitVec.ofNat 64 (g - j) ∧
        (∀ l < 4, prod (t.zproj l) =
          gacc (tabView Ctx W s.mem) (W + BitVec.ofNat 64 512) (W + BitVec.ofNat 64 1536) g l j) ∧
        (∀ r, r ≠ .rdx → r ≠ .r9 → r ≠ .r11 → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧
        t.wr = s.wr ∧ ZKeep [.xmm7, .xmm8, .xmm9, .xmm10, .xmm11, .xmm12] s t) ?_ (g - 0) s₁
      ⟨0, rfl, hg1, by rw [dx₁], by rw [r11₁, Nat.sub_zero], by rw [r9₁, Nat.sub_zero],
        fun l hl => by rw [p₁ l hl]; rfl, g₁, m₁, rd₁, wr₁, z₁.mono (by simp)⟩
    rintro n t ⟨j, rfl, hj, dxt, r11t, r9t, pt, gt, mt, rdt, wrt, zt⟩
    have h0t : ∀ l < 4, t.zlane .xmm0 l = revMask := fun l hl => by rw [zt _ (by decide) l hl, h0 l hl]
    refine WP.mono (ghStepP_ok t hj hg mt h0t dxt r11t (by rw [rdt, wrt]; exact wR (by omega_arith))
      (by rw [rdt, wrt]; exact cR (by omega_arith)) pt)
      fun t' ⟨p', dx', r11', r9', zf', g', m', rd', wr', z'⟩ => ?_
    have hz : t'.zf = some (decide (g - j = 1)) := by
      rw [zf', r9t, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, sub_beq (a := g - j) (b := 1) (by omega_arith)
        (by omega_arith)]
    have gg : ∀ r, r ≠ .rdx → r ≠ .r9 → r ≠ .r11 → t'.gpr r = s.gpr r := fun r a b c => by
      rw [g' r a b c, gt r a b c]
    by_cases he : j + 1 = g
    · left
      exact ⟨by simp [eval, hz]; omega_arith, fun l hl => by rw [p' l hl, he], gg, by rw [m', mt], by rw [rd', rdt],
        by rw [wr', wrt], zt.trans (z'.mono (by simp))⟩
    · right
      refine ⟨by simp [eval, hz]; omega_arith, g - (j + 1), by omega_arith, j + 1, rfl, by omega_arith, dx', r11', ?_, p', gg,
        by rw [m', mt], by rw [rd', rdt], by rw [wr', wrt], zt.trans (z'.mono (by simp))⟩
      rw [r9', r9t, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ofNat_sub (by omega_arith) (by omega_arith)]; congr 1
  · have h1t : ∀ l < 4, t.zlane .xmm1 l = poly := fun l hl => by rw [zt _ (by decide) l hl, h1 l hl]
    refine WP.mono (VG.Proof.Gcm.X86_64.StitchZ.fin_ok t h1t) fun t' ⟨y0, y1, f'⟩ => ⟨?_, y1, ?_, ?_, ?_, ?_, ?_⟩
    · rw [y0, pt 0 (by decide), pt 1 (by decide), pt 2 (by decide), pt 3 (by decide)]
    · intro r a b c; rw [f'.gpr, gt r a b c]
    · rw [f'.mem, mt]
    · rw [f'.rd, rdt]
    · rw [f'.wr, wrt]
    · intro r hr l hl
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      obtain ⟨n2, n7, n8, n9, n10, n11, n12⟩ := hr
      rw [f'.zlane r (by simp [n2, n8, n9, n10, n11]) l hl, zt r (by simp [n7, n8, n9, n10, n11, n12]) l hl]

/-! ## The short path with a prepared context -/

/-- With a prepared key context, `powersP` and `ghashP` compute what
`powers` and `ghash` do. -/
theorem powOk_powersP : PowOk CtxMode.prepared powersP ghashP := by
  intro s₀ Ctx W SP D n X
  refine ⟨tabView Ctx W, tabView_view X.cw X.cd, ghashP_ok X.cov, ?_⟩
  intro g s he _ hg1 hg8 f rd wr
  have hok : Spec.Gcm.PreparedPowersRepr s.mem Ctx :=
    CtxMode.prepared.frame f (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact X.cw
      · exact X.cd
      · exact X.ct.symm) X.w X.ok
  refine WP.mono (powersP_run s) fun t ⟨mt, z0, z1, gt, rdt, wrt⟩ =>
    ⟨by rw [mt]; exact tabView_ok hok hg8, by rw [mt]; exact Frame.refl _ _, z0, z1,
      fun r ha _ => gt r ha, rdt, wrt⟩

/-- `ghashP` in two runs. -/
theorem ghashP_taint : GhTaint ghashP := by
  intro s₀ s₀' Ctx W SP A D R al n J J' tl tl' h32
  have h32' := h32
  simp only [nb16] at h32'
  have hg8 : grp al n ≤ 8 := by simp only [grp, nb16]; omega_arith
  have hw : ∀ {s₀ : State} {J : Block} {tl : BitVec 64} (s : State), SJ s₀ Ctx W SP A D R al n J tl s →
      WP isa (.block ghSetupP) s fun t => t.gpr .rdx = W + BitVec.ofNat 64 384 ∧
        t.gpr .r9 = BitVec.ofNat 64 (grp al n) ∧ t.gpr .r11 = Ctx + BitVec.ofNat 64 (64 + 64 * grp al n) :=
    fun s h => WP.mono (ghSetupP_ok s h.sm.env.r13 h.sm.env.r15 h.sm.r288 hg8 (h.sm.env.perm.wR (by decide)))
      fun _ ⟨dx, r9, r11, _⟩ => ⟨dx, r9, r11⟩
  exact rel_piece [.rdx, .r9, .r11] (fun _ h => h.sm.env) (fun _ h => h.sm.env) (keepsEnv (by decide +kernel))
      ⟨_, by taint_decide⟩ hw hw (fun _ _ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h₁.1, h₂.1]
        · rw [h₁.2.1, h₂.2.1]
        · rw [h₁.2.2, h₂.2.2]) ⟨_, by taint_decide⟩

/-- `powersP` and `ghashP` in two runs: their addresses are the key
context's and `W`'s. -/
theorem powersP_ct : PowCT powersP ghashP := by
  refine ⟨fun {s₀ s₀' Ctx W SP A D R al n J J' tl tl'} => ?_, ghashP_taint⟩
  exact rel_env_regs [] (fun _ h => h.env) (fun _ h => h.env) (fun _ _ _ _ _ hr => by cases hr) ⟨_, by taint_decide⟩

end VG.Proof.AesGcm.X86_64.Short
