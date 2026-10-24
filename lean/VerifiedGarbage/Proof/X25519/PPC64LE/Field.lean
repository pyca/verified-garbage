module
public import VerifiedGarbage.Impl.X25519.PPC64LE
public import VerifiedGarbage.Proof.X25519.PPC64LE.Instr
public import VerifiedGarbage.Proof.X25519.PPC64LE.Limbs
import VerifiedGarbage.Proof.X25519.PPC64LE.Pass
public import VerifiedGarbage.Proof.X25519.Field

import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.X25519
public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# X25519 on PPC64LE: field elements in the working space

A field element is 8 words at an offset `o` of the working space at `B`
(`limb`), for the number `V` and its residue `FS`; every limb is below `2³²`
as a word. The carry out of a `pass` folded in again (`tail_ok`).
-/

@[expose] public section

namespace VG.Proof.X25519.PPC64LE

open VG VG.PPC64LE VG.Impl.X25519.PPC64LE
open VG.Spec.X25519 (P Fe)

/-- `r6` holds the working space `b`, at least 4096 writable bytes: X25519's
has 4096, Ed25519's on PPC64LE 8192. -/
structure Ctx (b : Addr) (s : State) : Prop where
  r6 : s.gpr .r6 = b
  wr : ∃ n, 4096 ≤ n ∧ (⟨b, n⟩ : Region) ∈ s.wr

theorem Ctx.of_rest {b : Addr} {s s' : State} {ws : List Reg} (h : Ctx b s) (hr : Rest ws s s')
    (h6 : Reg.r6 ∉ ws) : Ctx b s' :=
  ⟨by rw [hr.gpr _ h6, h.r6], by rw [hr.wr]; exact h.wr⟩

theorem Ctx.inW {b : Addr} {s : State} (h : Ctx b s) {d n : Nat} (hd : d + n ≤ 4096) :
    InRegions s.wr (b + BitVec.ofNat 64 d) n := by
  obtain ⟨k, hk, hw⟩ := h.wr
  exact in_base hw (by omega_using [hd, hk]) (by omega_using [hd])

theorem Ctx.inR {b : Addr} {s : State} (h : Ctx b s) {d n : Nat} (hd : d + n ≤ 4096) :
    InRegions (s.rd ++ s.wr) (b + BitVec.ofNat 64 d) n := by
  obtain ⟨k, hk, hw⟩ := h.wr
  exact in_base (List.mem_append_right _ hw) (by omega_using [hd, hk]) (by omega_using [hd])

/-- Limb `k` of the element at `o`. -/
def limb (m : Mem) (B : Addr) (o k : Nat) : Nat := wd m B (o + 4 * k)

theorem limb_lt (m : Mem) (B : Addr) (o k : Nat) : limb m B o k < 2 ^ 32 := wd_lt _ _ _

/-- The number of the element at `o`. -/
def V (m : Mem) (B : Addr) (o : Nat) : Nat := val32 (limb m B o) 8

/-- The element at `o`. -/
def FS (m : Mem) (B : Addr) (o : Nat) : Fe := Proof.X25519.toFe (V m B o)

theorem V_lt (m : Mem) (B : Addr) (o : Nat) : V m B o < 2 ^ 256 :=
  val32_lt fun k _ => limb_lt m B o k

/-- The limbs of an element in a frame that does not overlap it. -/
theorem limb_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {B : Addr} {o : Nat}
    (hd : ∀ r ∈ rs, ∀ k < 8, (⟨B + BitVec.ofNat 64 (o + 4 * k), 4⟩ : Region).Disjoint r) :
    ∀ k < 8, limb m' B o k = limb m B o k := fun k hk => wd_frame hf fun r hr => hd r hr k hk

/-- The clobbered registers of the field operations. -/
abbrev clob : List Reg := [.r4, .r5, .r7, .r8, .r9, .r10, .r11]

/-! ## Loading and storing a limb -/

theorem lw0_ok {b : Addr} {s : State} (hc : Ctx b s) {t : Reg} {d : Nat} (hd : d + 4 ≤ 4096)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Upd s s' t ((s.mem.readW (b + BitVec.ofNat 64 d) 32).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.load .w t .r6 d :: is)) s Q :=
  wp_lw (by decide) (by omega_using [hd]) (by rw [hc.r6]) (hc.inR hd) k

theorem sw0_ok {b : Addr} {s : State} (hc : Ctx b s) {t : Reg} {d : Nat} (hd : d + 4 ≤ 4096)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Mupd s s' (s.mem.writeW (b + BitVec.ofNat 64 d) ((s.gpr t).setWidth 32)) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.store .w t .r6 d :: is)) s Q :=
  wp_sw (by decide) (by omega_using [hd]) (by rw [hc.r6]) (hc.inW hd) k

theorem ldSrc_ok {b : Addr} {o k : Nat} {s : State} (hc : Ctx b s) (hd : o + 4 * k + 4 ≤ 4096) :
    WP isa (.block (ldSrc o k)) s fun s' =>
      (s'.gpr .r7).toNat = wd s.mem b (o + 4 * k) ∧ Rest [.r7] s s' ∧ s'.mem = s.mem :=
  lw0_ok hc hd fun s1 u1 => WP.block_nil ⟨by rw [u1.gpr, toNat_ext32]; rfl, u1.rest (by decide), u1.mem⟩

/-! ## The prologue -/

theorem prologue_ok {s : State} :
    WP isa (.block prologue) s fun s' =>
      s'.gpr .r10 = 38 ∧ s'.gpr .r8 = 0 ∧ Rest [.r8, .r10] s s' ∧ s'.mem = s.mem := by
  refine wp_li (by decide) fun s1 u1 => wp_li (by decide) fun s2 u2 => WP.block_nil ⟨?_, u2.gpr, ?_, ?_⟩
  · rw [u2.other _ (by decide), u1.gpr]; rfl
  · exact (u1.rest (by decide)).trans (u2.rest (by decide))
  · rw [u2.mem, u1.mem]

/-! ## The tail -/

theorem tail_ok {b : Addr} {o : Nat} (ho : o + 32 ≤ 4096) {s : State} (hc : Ctx b s)
    (h10 : s.gpr .r10 = 38) {c8 : Nat} (h8 : (s.gpr .r8).toNat = c8) (hc8 : c8 ≤ 38) :
    WP isa (.block (tail o)) s fun s' =>
      Rest [.r5, .r7, .r8] s s' ∧ Frame [⟨b + BitVec.ofNat 64 o, 32⟩] s.mem s'.mem ∧
      V s'.mem b o % P = (V s.mem b o + 2 ^ 256 * c8) % P := by
  have t38 : (38 : BitVec 64).toNat = 38 := rfl
  simp only [tail, List.cons_append, List.nil_append]
  refine wp_mul fun s1 u1 => ?_
  have e1 : (s1.gpr .r8).toNat = 38 * c8 := by
    rw [u1.gpr, h10, toNat_mul_lt (by rw [h8, t38]; omega_using [hc8]), h8, t38]; omega_using []
  have hc1 : Ctx b s1 := hc.of_rest (u1.rest (ws := [.r8]) (by decide)) (by decide)
  have hl : ∀ k < 8, limb s.mem b o k < 2 ^ 32 := fun k _ => limb_lt _ _ _ _
  refine WP.append (pass_ok (s0 := s1) (c := limb s.mem b o) (cin := 38 * c8)
    (by decide) (by decide) ho
    (fun k hk => by rw [hc1.r6]; exact hc1.inW (by omega_using [ho, hk]))
    e1 (fun k hk => by have := hl k hk; omega_using [this]) (by omega_using [hc8])
    (fun k hk s' hp => WP.mono (ldSrc_ok (hc1.of_rest hp.rest (by decide)) (by omega_using [ho, hk])) fun s'' h => ?_))
    fun s2 hp => ?_
  · refine ⟨?_, h.2.1.mono (by decide), h.2.2⟩
    rw [h.1, ← u1.mem]
    refine wd_frame hp.frame fun r hr => ?_
    rw [List.mem_singleton.mp hr, hc1.r6]
    exact Offset.disjoint _ (.inr (by omega_using [])) (by omega_using [ho, hk]) (by omega_using [ho, hk])
  · have hc2 : Ctx b s2 := hc1.of_rest hp.rest (by decide)
    have ht := tail_facts hl hc8
    have hpo : ∀ j < 8, wd s2.mem b (o + 4 * j) = out (limb s.mem b o) (38 * c8) j := fun j hj => by
      have := hp.outs j hj; rwa [hc1.r6] at this
    have hpf : Frame [⟨b + BitVec.ofNat 64 o, 4 * 8⟩] s1.mem s2.mem := by
      have := hp.frame; rwa [hc1.r6] at this
    refine wp_mul fun s3 u3 => ?_
    have e3 : (s3.gpr .r8).toNat = 38 * chain (limb s.mem b o) (38 * c8) 8 := by
      rw [u3.gpr, hp.rest.gpr .r10 (by decide), u1.other .r10 (by decide), h10,
        toNat_mul_lt (by rw [hp.r8, t38]; have := ht.1; omega_using [this]), hp.r8, t38]; omega_using []
    have hc3 : Ctx b s3 := hc2.of_rest (u3.rest (ws := [.r8]) (by decide)) (by decide)
    refine lw0_ok hc3 (by omega_using [ho]) fun s4 u4 => ?_
    refine wp_add fun s5 u5 => ?_
    have hc5 : Ctx b s5 :=
      hc3.of_rest ((u4.rest (ws := [.r7]) (by decide)).trans (u5.rest (by decide))) (by decide)
    refine sw0_ok hc5 (by omega_using [ho]) fun s6 u6 => WP.block_nil ?_
    have h0 := ht.2.1 0 (by decide)
    have o0 := hpo 0 (by decide)
    rw [Nat.mul_zero, Nat.add_zero] at o0
    have e5 : (s5.gpr .r7).toNat = tailL (limb s.mem b o) c8 0 := by
      rw [u5.gpr, u4.gpr, u4.other .r8 (by decide), u3.mem]
      simp only [tailL, ite_true] at h0 ⊢
      unfold wd at o0
      rw [toNat_add_lt (by rw [toNat_ext32, e3, o0]; omega_using [h0]), toNat_ext32, e3, o0]
    have hm6 : s6.mem = s2.mem.writeW (b + BitVec.ofNat 64 o) ((s5.gpr .r7).setWidth 32) := by
      rw [u6.mem, u5.mem, u4.mem, u3.mem]
    have hlimb : ∀ k < 8, limb s6.mem b o k = tailL (limb s.mem b o) c8 k := by
      intro k hk
      rw [limb, hm6]
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · rw [Nat.mul_zero, Nat.add_zero, wd_write_self, toNat_lo32, e5, Nat.mod_eq_of_lt h0]
      · rw [wd_write_other _ _ _ (by omega_using [hk0]) (by omega_using [ho, hk]) (by omega_using [ho]), hpo k hk]
        simp only [tailL, show k ≠ 0 by omega_using [hk0], ite_false]
    refine ⟨?_, ?_, ?_⟩
    · refine (u1.rest (ws := [.r5, .r7, .r8]) (by decide)).trans (hp.rest.trans ?_)
      refine (u3.rest (by decide)).trans ((u4.rest (by decide)).trans ((u5.rest (by decide)).trans ?_))
      exact u6.rest _
    · rw [hm6]
      refine (?_ : Frame _ s.mem s2.mem).writeW (List.mem_singleton_self _) _
        (Offset.contains b (d := o) (n := 32 / 8) (e := o) (k := 32) (Nat.le_refl _)
          (by omega_using []) (by omega_using [ho]))
      rw [← u1.mem]
      exact hpf
    · rw [V, val32_congr hlimb, ht.2.2]; rfl

end VG.Proof.X25519.PPC64LE
