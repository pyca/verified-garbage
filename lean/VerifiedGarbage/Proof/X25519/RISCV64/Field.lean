module

public import VerifiedGarbage.Impl.X25519.RISCV64
public import VerifiedGarbage.Proof.X25519.RISCV64.Instr
public import VerifiedGarbage.Proof.X25519.Limbs
public import VerifiedGarbage.Proof.X25519.Field
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.X25519
public import VerifiedGarbage.TCB.RISCV64.Isa
import VerifiedGarbage.Proof.Framework.Range

/-! ### `X25519.RISCV64.Pass`, which this module and modules that import it used -/

section

/-!
# X25519 on RISCV64: carrying sums into limbs

`pass rb o src` stores at `rb + o` the limbs of `Σ c_k 2^(32k) + cin`, from
the sums `c_k` that `src k` leaves in `a4` and the carry `cin` in `a5`
(`pass_ok`), for any `src` that computes them from the memory as it was, but
for the limbs already stored (`PassInv.frame`).
-/

@[expose] public section

namespace VG.Proof.X25519.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.X25519.RISCV64

theorem not_mem3 {r : Reg} (h : r ∉ [Reg.a2, .a4, .a5]) : r ≠ .a2 ∧ r ≠ .a4 ∧ r ≠ .a5 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  exact h

theorem carryStep_ok {rb : Reg} {off : Nat} {s : State} {a : Addr}
    (hrb : rb ≠ .a4) (ho : off < 2048)
    (ha : s.gpr rb + BitVec.ofNat 64 off = a) (hal : a.toNat % 4 = 0) (hw : InRegions s.wr a 4)
    (hs : (s.gpr .a4).toNat + (s.gpr .a5).toNat < 2 ^ 64) :
    WP isa (.block (carryStep rb off)) s fun s' =>
      (s'.gpr .a5).toNat = ((s.gpr .a4).toNat + (s.gpr .a5).toNat) / 2 ^ 32 ∧
      (∃ v : BitVec 32, v.toNat = ((s.gpr .a4).toNat + (s.gpr .a5).toNat) % 2 ^ 32 ∧
        s'.mem = s.mem.writeW a v) ∧
      Rest [.a4, .a5] s s' := by
  unfold carryStep
  refine wp_add fun s1 u1 => ?_
  refine wp_stw (a := a) ho (by rw [u1.other _ hrb]; exact ha) hal
    (by rw [u1.wr]; exact hw) fun s2 u2 => ?_
  refine wp_srl (by decide) fun s3 u3 => WP.block_nil ?_
  have e1 : (s1.gpr .a4).toNat = (s.gpr .a4).toNat + (s.gpr .a5).toNat := by
    rw [u1.gpr]; exact toNat_add_lt hs
  refine ⟨?_, ⟨(s1.gpr .a4).setWidth 32, ?_, ?_⟩, ?_⟩
  · rw [u3.gpr, u2.gpr, toNat_shr, e1]
  · rw [toNat_lo32, e1]
  · rw [u3.mem, u2.mem, u1.mem]
  · refine ⟨fun r hr => ?_, by rw [u3.rd, u2.rd, u1.rd], by rw [u3.wr, u2.wr, u1.wr],
      by rw [u3.sp, u2.sp, u1.sp]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u3.other _ hr.2, u2.gpr, u1.other _ hr.1]

/-- After `k` limbs of `pass rb o src` from `s0`, for the sums `c` and the
carry `cin`. -/
structure PassInv (rb : Reg) (o : Nat) (s0 : State) (c : Nat → Nat) (cin k : Nat) (s : State) :
    Prop where
  rest : Rest [.a2, .a4, .a5] s0 s
  a5 : (s.gpr .a5).toNat = chain c cin k
  frame : Frame [⟨s0.gpr rb + BitVec.ofNat 64 o, 4 * k⟩] s0.mem s.mem
  outs : ∀ j < k, wd s.mem (s0.gpr rb) (o + 4 * j) = out c cin j

theorem pass_ok {rb : Reg} {o : Nat} {src : Nat → List Instr} {s0 : State} {c : Nat → Nat}
    {cin : Nat} (hrb : rb ∉ [.a2, .a4, .a5]) (ho : o + 32 ≤ 2048)
    (hw : ∀ k < 8, InRegions s0.wr (s0.gpr rb + BitVec.ofNat 64 (o + 4 * k)) 4)
    (hal : ∀ k < 8, (s0.gpr rb + BitVec.ofNat 64 (o + 4 * k)).toNat % 4 = 0)
    (h8 : (s0.gpr .a5).toNat = cin)
    (hc : ∀ k < 8, c k + 2 ^ 32 ≤ 2 ^ 64) (hcin : cin < 2 ^ 32)
    (hsrc : ∀ k < 8, ∀ s, PassInv rb o s0 c cin k s →
      WP isa (.block (src k)) s fun s' =>
        (s'.gpr .a4).toNat = c k ∧ Rest [.a2, .a4] s s' ∧ s'.mem = s.mem) :
    WP isa (.block (pass rb o src)) s0 (PassInv rb o s0 c cin 8) := by
  have hr := not_mem3 hrb
  refine wp_range_flatMap (M := isa) (PassInv rb o s0 c cin) (fun k s hk h => ?_) 8 (Nat.le_refl _) s0
    ⟨Rest.refl _ _, by rw [h8]; rfl, Frame.refl _ _, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  refine WP.append (hsrc k hk s h) fun s1 ⟨h7, hr1, hm1⟩ => ?_
  have hrb1 : s1.gpr rb = s0.gpr rb := by
    rw [hr1.gpr _ (by simp [hr.1, hr.2.1]), h.rest.gpr _ hrb]
  have h81 : s1.gpr .a5 = s.gpr .a5 := hr1.gpr _ (by decide)
  have hsum := sum_lt hc hcin hk
  refine WP.mono (carryStep_ok (a := s0.gpr rb + BitVec.ofNat 64 (o + 4 * k))
    hr.2.1 (by omega_using [ho, hk]) (by rw [hrb1]) (hal k hk)
    (by rw [hr1.wr, h.rest.wr]; exact hw k hk)
    (by rw [h7, h81, h.a5]; exact hsum)) fun s2 ⟨e8, ⟨v, hv, hm2⟩, hr2⟩ => ?_
  rw [h7, h81, h.a5] at e8 hv
  rw [hm1] at hm2
  refine ⟨h.rest.trans ((hr1.mono (by decide)).trans (hr2.mono (by decide))), by rw [e8]; rfl, ?_,
    fun j hj => ?_⟩
  · rw [hm2]
    refine (h.frame.sub fun r hr' => ⟨_, List.mem_singleton_self _, ?_⟩).writeW
      (List.mem_singleton_self _) v (Offset.contains _ (Nat.le_add_right _ _) (by omega_using []) (by omega_using [ho, hk]))
    rw [List.mem_singleton.mp hr']
    exact Region.sub_prefix (by omega_using [])
  · rw [hm2]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [wd_write_other _ _ _ (by omega_using [hj]) (by omega_using [ho, hk, hj]) (by omega_using [ho, hk])]; exact h.outs j hj
    · rw [wd_write_self, hv]; rfl

end VG.Proof.X25519.RISCV64

end

end

/-!
# X25519 on RISCV64: field elements in the working space

A field element is 8 words at an offset `o` of the working space at `B`
(`limb`), for the number `V` and its residue `FS`; every limb is below `2³²`
as a word.
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
  wp_stw (by omega_using [hd]) (by rw [hc.a3]) (al4 hc.al hd4) (hc.inW hd) k

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

end VG.Proof.X25519.RISCV64
