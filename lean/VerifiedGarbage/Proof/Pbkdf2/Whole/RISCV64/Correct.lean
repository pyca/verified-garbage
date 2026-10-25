module

public import VerifiedGarbage.Proof.Pbkdf2.Whole.RISCV64.Block
import VerifiedGarbage.Proof.Pbkdf2.Whole.RISCV64.Loop
public import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Common
public import VerifiedGarbage.Proof.Pbkdf2.Whole.RISCV64.Contract

/-!
# PBKDF2 over any streaming hash function on RISC-V, the whole derivation: correctness

`i = 1` and no output written start the loop (`loopInit_ok`); after it,
`out` holds `T₁ ‖ … ‖ T_l` up to `out_len` bytes, which is PBKDF2's result
(`Whole.pbkdf2_eq`), and our caller's registers are restored (`main_ok`).
In its two frames, `pbkdf2` meets `pbkR` (`correct`), from the state its
inner frame's body starts in (`pre_alloc`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Whole.RISCV64

open VG.RISCV64
open VG.RISCV64.Steps (Upd Mupd wp_li)
open VG.Impl.Pbkdf2.Whole.RISCV64 (Fns)
open VG.Impl.Hmac.Stream.RISCV64 (Hash)
open VG.Proof.Hmac.Stream.RISCV64 (HashOK)
open VG.Proof.Hmac.Common (bytesAt_length)
open Spec.Sha256 (bytesAt)

variable {F : Fns}

theorem restorable : Spill.Restorable .s1 Fns.restList := by decide

section
variable {hF : FnsOK F} {s₀ : State} (hp : Pre F s₀)
include hp

omit hp in
/-- `i = 1`: `Inv` before the first block. -/
theorem loopInit_ok {s : State} (h : Keyed hF s₀ s) : WP isa (.block Fns.loopInit) s (Inv hF s₀ 0) := by
  unfold Fns.loopInit
  refine wp_li (by decide) fun s₁ u₁ => WP.block_nil ?_
  have d0 : dn s₀ (F := F) 0 = 0 := by show min (0 * F.H.D) _ = 0; simp
  refine ⟨h.kr.upd (by decide) u₁, by rw [u₁.mem]; exact h.st,
    by rw [u₁.other _ (by decide), h.s4, d0]; simp,
    by rw [u₁.other _ (by decide), h.s5, d0]; simp, by rw [u₁.gpr], by rw [Nat.zero_mul]; rfl, ?_⟩
  rw [d0]; rfl

/-- `pbkdf2` in its frames: our caller's registers are restored, and `out`
holds the derived key. -/
theorem main_ok : WP isa F.main s₀ fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧
      s'.gpr .ra = s₀.gpr .ra ∧ s'.sp = s₀.sp ∧ s'.wr = s₀.wr ∧
      bytesAt s'.mem (out s₀) (ol s₀) = (Gk hF s₀ (nbk s₀ (F := F))).take (ol s₀) := by
  have hz := sizes hF; have hl := layout (F := F); have hfr := hz.frB; have hD := hz.D
  unfold Fns.main
  refine WP.seq (WP.mono (prologue_ok hF hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (hi_ok' hF hp h₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (loopInit_ok h₂) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (loop_ok hp h₃) fun s₄ h₄ => ?_)
  refine WP.mono (Spill.restore_wp (b := .s1) (l := Fns.restList) (by omega_using [hp.al]) h₄.kr.s1
    (by decide) restorable
    (fun q hq => in_fr' hp h₄.kr.wr (by
      simp only [Fns.restList, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> omega) (by omega))
    (h₄.kr.saved.sub (by decide))) fun s₅ hr => ⟨fun r hr' => ?_, ?_, by rw [hr.sp, h₄.kr.sp],
      by rw [hr.wr, h₄.kr.wr], ?_⟩
  · refine hr.gpr_of ?_
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [.inr (h₄.kr.nv _ (by simp)), .inl (by decide), .inl (by decide), .inl (by decide),
      .inl (by decide), .inl (by decide), .inl (by decide), .inl (by decide), .inr (h₄.kr.nv _ (by simp)),
      .inr (h₄.kr.nv _ (by simp)), .inr (h₄.kr.nv _ (by simp)), .inr (h₄.kr.nv _ (by simp))]
  · exact hr.gpr_of (.inl (by decide))
  · rw [hr.mem]
    have e := h₄.outB
    rwa [show dn s₀ (F := F) (nbk s₀ (F := F)) = ol s₀ from Whole.done_nb hD.1] at e

end

/-! ## The frames -/

/-- The state the inner frame's body starts in, from `pbkdf2`'s precondition. -/
theorem pre_alloc (hF : FnsOK F) {s : State} (hp : (pbkR hF.hH.SH (F.itB + F.frB + F.X)).pre s) :
    Pre F (allocd F.frB (allocd F.itB s)) := by
  have hz := sizes hF; have hl := layout (F := F); have hfr := hz.frB; have hib := hz.itB; have hX := hz.X
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := hp
  rw [hF.hH.hD] at h14
  have hsp : (allocd F.frB (allocd F.itB s)).sp = s.sp - BitVec.ofNat 64 (F.itB + F.frB) := by
    simp only [allocd]; rw [BitVec.ofNat_add, Offset.sub_add_eq]
  have hspN : (s.sp - BitVec.ofNat 64 (F.itB + F.frB)).toNat = s.sp.toNat - (F.itB + F.frB) :=
    VG.Proof.Hmac.Stream.RISCV64.toNat_sub (by omega) (by omega)
  have hit : s.sp - BitVec.ofNat 64 F.itB =
      s.sp - BitVec.ofNat 64 (F.itB + F.frB) + BitVec.ofNat 64 F.frB := by
    rw [Offset.sub_ofNat_eq s.sp (a := F.itB) (b := F.itB + F.frB) (by omega), Nat.add_sub_cancel_left]
  have subF : Region.Sub ⟨s.sp - BitVec.ofNat 64 (F.itB + F.frB), F.frB⟩ (below s.sp (F.itB + F.frB + F.X)) :=
    Offset.sub_below s.sp (by omega) (by omega)
  have subI : Region.Sub ⟨s.sp - BitVec.ofNat 64 F.itB, F.itB⟩ (below s.sp (F.itB + F.frB + F.X)) :=
    Offset.sub_below s.sp (by omega) (by omega)
  have subS : Region.Sub (below (s.sp - BitVec.ofNat 64 (F.itB + F.frB)) F.X) (below s.sp (F.itB + F.frB + F.X)) := by
    have := below_body' s.sp (F.itB + F.frB) F.X
    rwa [Nat.add_comm F.X] at this
  have subI' : Region.Sub (itR F (allocd F.frB (allocd F.itB s))) (below s.sp (F.itB + F.frB + F.X)) := by
    show Region.Sub ⟨(allocd F.frB (allocd F.itB s)).sp + BitVec.ofNat 64 F.frB, F.itB⟩ _
    rw [hsp, ← hit]; exact subI
  have subF' : Region.Sub (frR F (allocd F.frB (allocd F.itB s))) (below s.sp (F.itB + F.frB + F.X)) := by
    show Region.Sub ⟨(allocd F.frB (allocd F.itB s)).sp, F.frB⟩ _
    rw [hsp]; exact subF
  have subS' : Region.Sub (stk F (allocd F.frB (allocd F.itB s))) (below s.sp (F.itB + F.frB + F.X)) := by
    show Region.Sub (below (allocd F.frB (allocd F.itB s)).sp F.X) _
    rw [hsp]; exact subS
  refine ⟨h1, ?_, h3, h4, h7.sub_left subF', h8.sub_left subF', h9.sub_left subF', h7.sub_left subI',
    h8.sub_left subI', h9.sub_left subI', ?_, ?_, ?_, h7.sub_left subS', h8.sub_left subS', h9.sub_left subS',
    h10, h11, h12, h13, h14⟩
  · show (⟨(allocd F.frB (allocd F.itB s)).sp, F.frB⟩ : Region) :: ⟨s.sp - BitVec.ofNat 64 F.itB, F.itB⟩ ::
      s.wr = _
    rw [h2, hit, ← hsp]; rfl
  · rw [hsp, hspN]; omega
  · rw [hsp, hspN]; omega
  · rw [hsp, hspN]; have := s.sp.isLt; omega

variable (hF : FnsOK F)

/-- `pbkdf2`, with its frames. -/
theorem correct {s : State} (hp : (pbkR hF.hH.SH (F.itB + F.frB + F.X)).pre s) :
    WP isa F.pbkdf2 s fun s' => abiPreserved s s' ∧ (pbkR hF.hH.SH (F.itB + F.frB + F.X)).post s s' := by
  have hz := sizes hF; have hl := layout (F := F); have hfr := hz.frB; have hib := hz.itB; have hD := hz.D
  have hsp : F.itB + F.frB + F.X ≤ s.sp.toNat := hp.2.2.2.2.2.1
  have hal : s.sp.toNat % 16 = 0 := hp.2.2.2.2.1
  have hspN : (allocd F.itB s).sp.toNat = s.sp.toNat - F.itB :=
    VG.Proof.Hmac.Stream.RISCV64.toNat_sub (by omega) (by omega)
  have p := pre_alloc hF hp
  unfold Fns.pbkdf2
  refine WP.alloc ⟨by have := hF.itW0; omega, hib, hl.2.2.2.2.2.2.2.2.2.2⟩ (by omega)
    (WP.alloc ⟨by omega, hfr, hl.2.2.2.2.2.2.2.2.1⟩ (by rw [hspN]; omega)
      (WP.mono (main_ok (hF := hF) p) fun s' ⟨hk, hra, hsp', hwr, hb⟩ => ?_))
  rw [freed_eq hwr hsp']
  rw [freed_eq (s₂ := { s' with sp := (allocd F.itB s).sp, wr := (allocd F.itB s).wr }) rfl rfl]
  refine ⟨⟨fun r hr => hk r hr, rfl, hra⟩, ?_⟩
  show _ = some (bytesAt s'.mem (out s) (ol s))
  rw [show out s = out (allocd F.frB (allocd F.itB s)) from rfl, show ol s = ol (allocd F.frB (allocd F.itB s)) from rfl,
    hb]
  refine Whole.pbkdf2_eq _ _ (by rw [hF.hH.hD]; exact p.olD) ?_
  rw [hF.hH.hD]
  rfl

end VG.Proof.Pbkdf2.Whole.RISCV64
