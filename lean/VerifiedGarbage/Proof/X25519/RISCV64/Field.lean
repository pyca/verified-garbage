module
public import VerifiedGarbage.Impl.X25519.RISCV64
public import VerifiedGarbage.Proof.X25519.RISCV64.Instr
public import VerifiedGarbage.Proof.X25519.Limbs
import VerifiedGarbage.Proof.X25519.RISCV64.Pass
public import VerifiedGarbage.Proof.X25519.Field

import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.X25519
public import VerifiedGarbage.TCB.RISCV64.Isa

/-!
# X25519 on RISCV64: field elements in the working space

A field element is 8 words at an offset `o` of the working space at `B`
(`limb`), for the number `V` and its residue `FS`; every limb is below `2³²`
as a word. The carry out of a `pass` folded in again (`tail_ok`).
-/

@[expose] public section

namespace VG.Proof.X25519.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.X25519.RISCV64
open VG.Spec.X25519 (P Fe)

/-- `a3` holds the working space `b`, a multiple of 8 (the working space
rounded up), followed by at least 2048 writable bytes, all that offsets in
the immediates of loads and stores reach. -/
structure Ctx (b : Addr) (s : State) : Prop where
  a3 : s.gpr .a3 = b
  al : b.toNat % 8 = 0
  wr : ∀ d n, d + n ≤ 2048 → InRegions s.wr (b + BitVec.ofNat 64 d) n

theorem Ctx.of_rest {b : Addr} {s s' : State} {ws : List Reg} (h : Ctx b s) (hr : Rest ws s s')
    (h6 : Reg.a3 ∉ ws) : Ctx b s' :=
  ⟨by rw [hr.gpr _ h6, h.a3], h.al, by rw [hr.wr]; exact h.wr⟩

theorem Ctx.inW {b : Addr} {s : State} (h : Ctx b s) {d n : Nat} (hd : d + n ≤ 2048) :
    InRegions s.wr (b + BitVec.ofNat 64 d) n :=
  h.wr d n hd

theorem Ctx.inR {b : Addr} {s : State} (h : Ctx b s) {d n : Nat} (hd : d + n ≤ 2048) :
    InRegions (s.rd ++ s.wr) (b + BitVec.ofNat 64 d) n :=
  let ⟨r, hr, hc⟩ := h.wr d n hd
  ⟨r, List.mem_append_right _ hr, hc⟩

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
abbrev clob : List Reg := [.a1, .a2, .a4, .a5, .a6, .a7, .t0]

/-! ## Loading and storing a limb -/

theorem lw0_ok {b : Addr} {s : State} (hc : Ctx b s) {t : Reg} {d : Nat} (hd : d + 4 ≤ 2048)
    (hd4 : d % 4 = 0) {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Upd s s' t ((s.mem.readW (b + BitVec.ofNat 64 d) 32).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.load .w t .a3 d :: is)) s Q :=
  wp_lw (by omega_using [hd]) (by rw [hc.a3]) (al4 hc.al hd4) (hc.inR hd) k

theorem sw0_ok {b : Addr} {s : State} (hc : Ctx b s) {t : Reg} {d : Nat} (hd : d + 4 ≤ 2048)
    (hd4 : d % 4 = 0) {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Mupd s s' (s.mem.writeW (b + BitVec.ofNat 64 d) ((s.gpr t).setWidth 32)) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.store .w t .a3 d :: is)) s Q :=
  wp_sw (by omega_using [hd]) (by rw [hc.a3]) (al4 hc.al hd4) (hc.inW hd) k

theorem ldSrc_ok {b : Addr} {o k : Nat} {s : State} (hc : Ctx b s) (hd : o + 4 * k + 4 ≤ 2048)
    (ho4 : o % 4 = 0) :
    WP isa (.block (ldSrc o k)) s fun s' =>
      (s'.gpr .a4).toNat = wd s.mem b (o + 4 * k) ∧ Rest [.a4] s s' ∧ s'.mem = s.mem :=
  lw0_ok hc hd (by omega_using [ho4]) fun s1 u1 => WP.block_nil ⟨by rw [u1.gpr, toNat_ext32]; rfl, u1.rest (by decide), u1.mem⟩

/-! ## The prologue -/

theorem prologue_ok {s : State} :
    WP isa (.block prologue) s fun s' =>
      s'.gpr .a7 = 38 ∧ s'.gpr .a5 = 0 ∧ Rest [.a5, .a7] s s' ∧ s'.mem = s.mem := by
  refine wp_li (by decide) fun s1 u1 => wp_li (by decide) fun s2 u2 => WP.block_nil ⟨?_, u2.gpr, ?_, ?_⟩
  · rw [u2.other _ (by decide), u1.gpr]; rfl
  · exact (u1.rest (by decide)).trans (u2.rest (by decide))
  · rw [u2.mem, u1.mem]

/-! ## The tail -/

theorem tail_ok {b : Addr} {o : Nat} (ho : o + 32 ≤ 2048) (ho4 : o % 4 = 0) {s : State} (hc : Ctx b s)
    (h10 : s.gpr .a7 = 38) {c8 : Nat} (h8 : (s.gpr .a5).toNat = c8) (hc8 : c8 ≤ 38) :
    WP isa (.block (tail o)) s fun s' =>
      Rest [.a2, .a4, .a5] s s' ∧ Frame [⟨b + BitVec.ofNat 64 o, 32⟩] s.mem s'.mem ∧
      V s'.mem b o % P = (V s.mem b o + 2 ^ 256 * c8) % P := by
  have t38 : (38 : BitVec 64).toNat = 38 := rfl
  simp only [tail, List.cons_append, List.nil_append]
  refine wp_mul fun s1 u1 => ?_
  have e1 : (s1.gpr .a5).toNat = 38 * c8 := by
    rw [u1.gpr, h10, toNat_mul_lt (by rw [h8, t38]; omega_using [hc8]), h8, t38]; omega_using []
  have hc1 : Ctx b s1 := hc.of_rest (u1.rest (ws := [.a5]) (by decide)) (by decide)
  have hl : ∀ k < 8, limb s.mem b o k < 2 ^ 32 := fun k _ => limb_lt _ _ _ _
  refine WP.append (pass_ok (s0 := s1) (c := limb s.mem b o) (cin := 38 * c8)
    (by decide) ho
    (fun k hk => by rw [hc1.a3]; exact hc1.inW (by omega_using [ho, hk]))
    (fun _ _ => by rw [hc1.a3]; exact al4 hc1.al (by omega_using [ho4]))
    e1 (fun k hk => by have := hl k hk; omega_using [this]) (by omega_using [hc8])
    (fun k hk s' hp => WP.mono (ldSrc_ok (hc1.of_rest hp.rest (by decide)) (by omega_using [ho, hk]) ho4) fun s'' h => ?_))
    fun s2 hp => ?_
  · refine ⟨?_, h.2.1.mono (by decide), h.2.2⟩
    rw [h.1, ← u1.mem]
    refine wd_frame hp.frame fun r hr => ?_
    rw [List.mem_singleton.mp hr, hc1.a3]
    exact Offset.disjoint _ (.inr (by omega_using [])) (by omega_using [ho, hk]) (by omega_using [ho, hk])
  · have hc2 : Ctx b s2 := hc1.of_rest hp.rest (by decide)
    have ht := tail_facts hl hc8
    have hpo : ∀ j < 8, wd s2.mem b (o + 4 * j) = out (limb s.mem b o) (38 * c8) j := fun j hj => by
      have := hp.outs j hj; rwa [hc1.a3] at this
    have hpf : Frame [⟨b + BitVec.ofNat 64 o, 4 * 8⟩] s1.mem s2.mem := by
      have := hp.frame; rwa [hc1.a3] at this
    refine wp_mul fun s3 u3 => ?_
    have e3 : (s3.gpr .a5).toNat = 38 * chain (limb s.mem b o) (38 * c8) 8 := by
      rw [u3.gpr, hp.rest.gpr .a7 (by decide), u1.other .a7 (by decide), h10,
        toNat_mul_lt (by rw [hp.a5, t38]; have := ht.1; omega_using [this]), hp.a5, t38]; omega_using []
    have hc3 : Ctx b s3 := hc2.of_rest (u3.rest (ws := [.a5]) (by decide)) (by decide)
    refine lw0_ok hc3 (by omega_using [ho]) ho4 fun s4 u4 => ?_
    refine wp_add fun s5 u5 => ?_
    have hc5 : Ctx b s5 :=
      hc3.of_rest ((u4.rest (ws := [.a4]) (by decide)).trans (u5.rest (by decide))) (by decide)
    refine sw0_ok hc5 (by omega_using [ho]) ho4 fun s6 u6 => WP.block_nil ?_
    have h0 := ht.2.1 0 (by decide)
    have o0 := hpo 0 (by decide)
    rw [Nat.mul_zero, Nat.add_zero] at o0
    have e5 : (s5.gpr .a4).toNat = tailL (limb s.mem b o) c8 0 := by
      rw [u5.gpr, u4.gpr, u4.other .a5 (by decide), u3.mem]
      simp only [tailL, ite_true] at h0 ⊢
      unfold wd at o0
      rw [toNat_add_lt (by rw [toNat_ext32, e3, o0]; omega_using [h0]), toNat_ext32, e3, o0]
    have hm6 : s6.mem = s2.mem.writeW (b + BitVec.ofNat 64 o) ((s5.gpr .a4).setWidth 32) := by
      rw [u6.mem, u5.mem, u4.mem, u3.mem]
    have hlimb : ∀ k < 8, limb s6.mem b o k = tailL (limb s.mem b o) c8 k := by
      intro k hk
      rw [limb, hm6]
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · rw [Nat.mul_zero, Nat.add_zero, wd_write_self, toNat_lo32, e5, Nat.mod_eq_of_lt h0]
      · rw [wd_write_other _ _ _ (by omega_using [hk0]) (by omega_using [ho, hk]) (by omega_using [ho]), hpo k hk]
        simp only [tailL, show k ≠ 0 by omega_using [hk0], ite_false]
    refine ⟨?_, ?_, ?_⟩
    · refine (u1.rest (ws := [.a2, .a4, .a5]) (by decide)).trans (hp.rest.trans ?_)
      refine (u3.rest (by decide)).trans ((u4.rest (by decide)).trans ((u5.rest (by decide)).trans ?_))
      exact u6.rest _
    · rw [hm6]
      refine (?_ : Frame _ s.mem s2.mem).writeW (List.mem_singleton_self _) _
        (Offset.contains b (d := o) (n := 32 / 8) (e := o) (k := 32) (Nat.le_refl _)
          (by omega_using []) (by omega_using [ho]))
      rw [← u1.mem]
      exact hpf
    · rw [V, val32_congr hlimb, ht.2.2]; rfl

end VG.Proof.X25519.RISCV64
