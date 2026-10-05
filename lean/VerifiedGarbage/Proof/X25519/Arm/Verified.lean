import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Impl.X25519.Arm
import VerifiedGarbage.Proof.X25519.Bytes
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Spec.X25519.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.Arm.Pass`. -/
section

/-!
# X25519 on 32-bit ARM: carrying sums into limbs

`pass rb o src` stores at `[rb, #o]` the limbs of `Σ c_k 2^(16k) + cin`, from
the sums `c_k` that `src k` leaves in `r3` and the carry `cin` in `r5`
(`pass_ok`), for any `src` that computes them from the memory as it was, but
for the limbs already stored (`PassInv.frame`).
-/

namespace VG.Proof.X25519.Arm

open VG VG.Arm VG.Impl.X25519.Arm

theorem not_mem4 {r : Reg} (h : r ∉ [Reg.r2, .r3, .r4, .r5]) :
    r ≠ .r2 ∧ r ≠ .r3 ∧ r ≠ .r4 ∧ r ≠ .r5 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  exact h

theorem carryStep_ok {rb : Reg} {off : Nat} {s : State} {a : Addr}
    (hrb : rb ≠ .r3 ∧ rb ≠ .r4) (ho : off < 4096)
    (ha : State.addr (s.gpr rb + BitVec.ofNat 32 off) = a) (hw : InRegions s.wr a 4)
    (h6 : s.gpr .r6 = mask16) (hs : (s.gpr .r3).toNat + (s.gpr .r5).toNat < 2 ^ 32) :
    WP isa (.block (carryStep rb off)) s fun s' =>
      (s'.gpr .r5).toNat = ((s.gpr .r3).toNat + (s.gpr .r5).toNat) / 65536 ∧
      (∃ v : BitVec 32, v.toNat = ((s.gpr .r3).toNat + (s.gpr .r5).toNat) % 65536 ∧
        s'.mem = s.mem.writeW a v) ∧
      Rest [.r3, .r4, .r5] s s' := by
  unfold carryStep
  refine wp_dp (op2_reg _ _) fun s1 u1 => ?_
  refine wp_dp (op2_reg _ _) fun s2 u2 => ?_
  refine wp_str (a := a) ho (by rw [u2.other _ hrb.2, u1.other _ hrb.1]; exact ha)
    (by rw [u2.wr, u1.wr]; exact hw) fun s3 u3 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s4 u4 => WP.block_nil ?_
  have e1 : (s1.gpr .r3).toNat = (s.gpr .r3).toNat + (s.gpr .r5).toNat := by
    rw [u1.gpr]; exact toNat_add_lt hs
  refine ⟨?_, ⟨s2.gpr .r4, ?_, ?_⟩, ?_⟩
  · rw [u4.gpr, u3.gpr, u2.other _ (by decide), toNat_shr, e1]
  · rw [u2.gpr, u1.other .r6 (by decide), h6]
    show (s1.gpr .r3 &&& mask16).toNat = _
    rw [toNat_and_mask16, e1]
  · rw [u4.mem, u3.mem, u2.mem, u1.mem]
  · refine ⟨fun r hr => ?_, by rw [u4.rd, u3.rd, u2.rd, u1.rd], by rw [u4.wr, u3.wr, u2.wr, u1.wr],
      by rw [u4.sp, u3.sp, u2.sp, u1.sp]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u4.other _ hr.2.2, u3.gpr, u2.other _ hr.2.1, u1.other _ hr.1]

/-- After `k` limbs of `pass rb o src` from `s0`, for the sums `c` and the
carry `cin`. -/
structure PassInv (rb : Reg) (o : Nat) (s0 : State) (c : Nat → Nat) (cin k : Nat) (s : State) :
    Prop where
  rest : Rest [.r2, .r3, .r4, .r5] s0 s
  r5 : (s.gpr .r5).toNat = chain c cin k
  frame : Frame [⟨State.addr (s0.gpr rb) + BitVec.ofNat 64 o, 4 * k⟩] s0.mem s.mem
  outs : ∀ j < k, wd s.mem (State.addr (s0.gpr rb)) (o + 4 * j) = VG.Proof.X25519.Arm.out c cin j

theorem pass_ok {rb : Reg} {o : Nat} {src : Nat → List Instr} {s0 : State} {c : Nat → Nat}
    {cin : Nat} (hrb : rb ∉ [.r2, .r3, .r4, .r5]) (ho : o + 64 ≤ 4096)
    (hfit : (s0.gpr rb).toNat + o + 64 ≤ 2 ^ 32)
    (hw : ∀ k < 16, InRegions s0.wr (State.addr (s0.gpr rb) + BitVec.ofNat 64 (o + 4 * k)) 4)
    (h6 : s0.gpr .r6 = mask16) (h5 : (s0.gpr .r5).toNat = cin)
    (hc : ∀ k < 16, c k + 65536 ≤ 2 ^ 32) (hcin : cin < 65536)
    (hsrc : ∀ k < 16, ∀ s, VG.Proof.X25519.Arm.PassInv rb o s0 c cin k s →
      WP isa (.block (src k)) s fun s' =>
        (s'.gpr .r3).toNat = c k ∧ Rest [.r2, .r3, .r4] s s' ∧ s'.mem = s.mem) :
    WP isa (.block (pass rb o src)) s0 (VG.Proof.X25519.Arm.PassInv rb o s0 c cin 16) := by
  have hr := VG.Proof.X25519.Arm.not_mem4 hrb
  refine wp_range_flatMap (M := isa) (VG.Proof.X25519.Arm.PassInv rb o s0 c cin) (fun k s hk h => ?_) 16 (Nat.le_refl _) s0
    ⟨Rest.refl _ _, by rw [h5]; rfl, Frame.refl _ _, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  refine WP.append (hsrc k hk s h) fun s1 ⟨h3, hr1, hm1⟩ => ?_
  have hrb1 : s1.gpr rb = s0.gpr rb := by
    rw [hr1.gpr _ (by simp [hr.1, hr.2.1, hr.2.2.1]), h.rest.gpr _ hrb]
  have h51 : s1.gpr .r5 = s.gpr .r5 := hr1.gpr _ (by decide)
  have hsum := sum_lt hc hcin hk
  refine WP.mono (VG.Proof.X25519.Arm.carryStep_ok (a := State.addr (s0.gpr rb) + BitVec.ofNat 64 (o + 4 * k))
    ⟨hr.2.1, hr.2.2.1⟩ (by omega) (by rw [hrb1]; exact VG.Proof.X25519.Arm.ea (by omega))
    (by rw [hr1.wr, h.rest.wr]; exact hw k hk)
    (by rw [hr1.gpr _ (by decide), h.rest.gpr _ (by decide), h6])
    (by rw [h3, h51, h.r5]; exact hsum)) fun s2 ⟨e5, ⟨v, hv, hm2⟩, hr2⟩ => ?_
  rw [h3, h51, h.r5] at e5 hv
  rw [hm1] at hm2
  refine ⟨h.rest.trans ((hr1.mono (by decide)).trans (hr2.mono (by decide))), by rw [e5]; rfl, ?_,
    fun j hj => ?_⟩
  · rw [hm2]
    refine (h.frame.sub fun r hr' => ⟨_, List.mem_singleton_self _, ?_⟩).writeW
      (List.mem_singleton_self _) v (Offset.contains _ (Nat.le_add_right _ _) (by omega) (by omega))
    rw [List.mem_singleton.mp hr']
    exact Region.sub_prefix (by omega)
  · rw [hm2]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [wd_write_other _ _ _ (by omega) (by omega) (by omega)]; exact h.outs j hj
    · rw [wd_write_self, hv]; rfl

end VG.Proof.X25519.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.Arm.Field`. -/
section

/-!
# X25519 on 32-bit ARM: field elements in the working space

A field element is 16 words at an offset `o` of the working space at `B`
(`limb`), each below `2¹⁶` (`Lim`), for the number `V` and its residue `FS`.
The carry out of a `pass` folded in again (`tail_ok`), and `add` and `sub`
(`add_ok`, `sub_ok`).

An offset from `r0` in a load or store is below 4096, so the lemmas hold for
a working space of those 4096 bytes and `e` more (`CtxN e`): X25519's has
none (`Ctx`); Ed25519's on ARMv7 has 8192 bytes.
-/

namespace VG.Proof.X25519.Arm

open VG VG.Arm VG.Impl.X25519.Arm
open VG.Spec.X25519 (P Fe)

/-- `r0` holds the working space `b`, `4096 + e` writable bytes. -/
structure CtxN (e : Nat) (b : BitVec 32) (s : State) : Prop where
  r0 : s.gpr .r0 = b
  fit : b.toNat + (4096 + e) ≤ 2 ^ 32
  wr : (⟨State.addr b, 4096 + e⟩ : Region) ∈ s.wr

/-- X25519's working space, 4096 bytes. -/
abbrev Ctx := VG.Proof.X25519.Arm.CtxN 0

section
variable {e : Nat}

theorem CtxN.of_rest {b : BitVec 32} {s s' : State} {ws : List Reg} (h : VG.Proof.X25519.Arm.CtxN e b s) (hr : Rest ws s s')
    (h0 : Reg.r0 ∉ ws) : VG.Proof.X25519.Arm.CtxN e b s' :=
  ⟨by rw [hr.gpr _ h0, h.r0], h.fit, by rw [hr.wr]; exact h.wr⟩

theorem CtxN.ea {b : BitVec 32} {s : State} (h : VG.Proof.X25519.Arm.CtxN e b s) {d : Nat} (hd : d < 4096) :
    State.addr (s.gpr .r0 + BitVec.ofNat 32 d) = State.addr b + BitVec.ofNat 64 d := by
  rw [h.r0]; exact addr_add (by have := h.fit; omega)

theorem CtxN.inW {b : BitVec 32} {s : State} (h : VG.Proof.X25519.Arm.CtxN e b s) {d n : Nat} (hd : d + n ≤ 4096) :
    InRegions s.wr (State.addr b + BitVec.ofNat 64 d) n := in_base h.wr (by omega) (by omega)

theorem CtxN.inR {b : BitVec 32} {s : State} (h : VG.Proof.X25519.Arm.CtxN e b s) {d n : Nat} (hd : d + n ≤ 4096) :
    InRegions (s.rd ++ s.wr) (State.addr b + BitVec.ofNat 64 d) n :=
  in_base (List.mem_append_right _ h.wr) (by omega) (by omega)

end

/-- Limb `k` of the element at `o`. -/
def limb (m : Mem) (B : Addr) (o k : Nat) : Nat := wd m B (o + 4 * k)

/-- Every limb of the element at `o` is below `2¹⁶`. -/
def Lim (m : Mem) (B : Addr) (o : Nat) : Prop := ∀ k < 16, VG.Proof.X25519.Arm.limb m B o k < 65536

/-- The number of the element at `o`. -/
def V (m : Mem) (B : Addr) (o : Nat) : Nat := val16 (VG.Proof.X25519.Arm.limb m B o) 16

/-- The element at `o`. -/
def FS (m : Mem) (B : Addr) (o : Nat) : Fe := Proof.X25519.toFe (VG.Proof.X25519.Arm.V m B o)

theorem V_lt {m : Mem} {B : Addr} {o : Nat} (h : VG.Proof.X25519.Arm.Lim m B o) : VG.Proof.X25519.Arm.V m B o < 2 ^ 256 := val16_lt h

/-- The limbs of an element in a frame that does not overlap it. -/
theorem limb_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {B : Addr} {o : Nat}
    (hd : ∀ r ∈ rs, ∀ k < 16, (⟨B + BitVec.ofNat 64 (o + 4 * k), 4⟩ : Region).Disjoint r) :
    ∀ k < 16, VG.Proof.X25519.Arm.limb m' B o k = VG.Proof.X25519.Arm.limb m B o k := fun k hk => wd_frame hf fun r hr => hd r hr k hk

/-- The words of `[o, o + 64)` are outside the ranges `[p.1, p.1 + p.2)`
of `l`, all within the working space. -/
def Outside (o : Nat) (l : List (Nat × Nat)) : Bool :=
  l.all fun p => o + 64 ≤ p.1 || p.1 + p.2 ≤ o

/-- The ranges `l` of the working space at `B`. -/
def offR (B : Addr) (l : List (Nat × Nat)) : List Region :=
  l.map fun p => ⟨B + BitVec.ofNat 64 p.1, p.2⟩

theorem limb_offR {l : List (Nat × Nat)} {m m' : Mem} {B : Addr} (hf : Frame (VG.Proof.X25519.Arm.offR B l) m m') {o : Nat}
    (ho : VG.Proof.X25519.Arm.Outside o l = true) (hl : (l.all fun p => p.1 + p.2 ≤ 4096) = true) (ho' : o + 64 ≤ 4096) :
    ∀ k < 16, VG.Proof.X25519.Arm.limb m' B o k = VG.Proof.X25519.Arm.limb m B o k := by
  refine VG.Proof.X25519.Arm.limb_frame hf fun r hr k hk => ?_
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
  have h1 := List.all_eq_true.mp ho p hp
  have h2 := List.all_eq_true.mp hl p hp
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h1 h2
  exact Offset.disjoint B (by omega) (by omega) (by omega)

theorem Lim_offR {l : List (Nat × Nat)} {m m' : Mem} {B : Addr} (hf : Frame (VG.Proof.X25519.Arm.offR B l) m m') {o : Nat}
    (ho : VG.Proof.X25519.Arm.Outside o l = true) (hl : (l.all fun p => p.1 + p.2 ≤ 4096) = true) (ho' : o + 64 ≤ 4096)
    (h : VG.Proof.X25519.Arm.Lim m B o) : VG.Proof.X25519.Arm.Lim m' B o := fun k hk => by rw [VG.Proof.X25519.Arm.limb_offR hf ho hl ho' k hk]; exact h k hk

theorem V_offR {l : List (Nat × Nat)} {m m' : Mem} {B : Addr} (hf : Frame (VG.Proof.X25519.Arm.offR B l) m m') {o : Nat}
    (ho : VG.Proof.X25519.Arm.Outside o l = true) (hl : (l.all fun p => p.1 + p.2 ≤ 4096) = true) (ho' : o + 64 ≤ 4096) :
    VG.Proof.X25519.Arm.V m' B o = VG.Proof.X25519.Arm.V m B o := val16_congr (VG.Proof.X25519.Arm.limb_offR hf ho hl ho')

/-- The clobbered registers of the field operations. -/
abbrev clob : List Reg := [.r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9]

section
variable {e : Nat}

/-! ## Loading a limb -/

theorem ldr0_ok {b : BitVec 32} {s : State} (hc : VG.Proof.X25519.Arm.CtxN e b s) {t : Reg} {d : Nat} (hd : d + 4 ≤ 4096)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Upd s s' t (s.mem.readW (State.addr b + BitVec.ofNat 64 d) 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.ldr t .r0 d :: is)) s Q :=
  wp_ldr (by omega) (hc.ea (by omega)) (hc.inR hd) k

theorem str0_ok {b : BitVec 32} {s : State} (hc : VG.Proof.X25519.Arm.CtxN e b s) {t : Reg} {d : Nat} (hd : d + 4 ≤ 4096)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Mupd s s' (s.mem.writeW (State.addr b + BitVec.ofNat 64 d) (s.gpr t)) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.str t .r0 d :: is)) s Q :=
  wp_str (by omega) (hc.ea (by omega)) (hc.inW hd) k

theorem ldSrc_ok {b : BitVec 32} {o k : Nat} {s : State} (hc : VG.Proof.X25519.Arm.CtxN e b s) (hd : o + 4 * k + 4 ≤ 4096) :
    WP isa (.block (ldSrc o k)) s fun s' =>
      (s'.gpr .r3).toNat = wd s.mem (State.addr b) (o + 4 * k) ∧ Rest [.r3] s s' ∧ s'.mem = s.mem :=
  VG.Proof.X25519.Arm.ldr0_ok hc hd fun s1 u1 => WP.block_nil ⟨by rw [u1.gpr]; rfl, u1.rest (by decide), u1.mem⟩

/-! ## The prologue -/

theorem prologue_ok {s : State} :
    WP isa (.block prologue) s fun s' =>
      s'.gpr .r6 = mask16 ∧ s'.gpr .r8 = 38 ∧ s'.gpr .r5 = 0 ∧ Rest [.r5, .r6, .r8] s s' ∧
        s'.mem = s.mem := by
  refine wp_movw fun s1 u1 => wp_mov (op2_imm (by decide)) fun s2 u2 =>
    wp_mov (op2_imm (by decide)) fun s3 u3 => WP.block_nil ⟨?_, ?_, u3.gpr, ?_, ?_⟩
  · rw [u3.other _ (by decide), u2.other _ (by decide), u1.gpr]
  · rw [u3.other _ (by decide), u2.gpr]
  · exact (u1.rest (by decide)).trans ((u2.rest (by decide)).trans (u3.rest (by decide)))
  · rw [u3.mem, u2.mem, u1.mem]

/-! ## The tail -/

theorem tail_ok {b : BitVec 32} {o : Nat} (ho : o + 64 ≤ 4096) {s : State} (hc : VG.Proof.X25519.Arm.CtxN e b s)
    (h6 : s.gpr .r6 = mask16) (h8 : s.gpr .r8 = 38) {c16 : Nat} (h5 : (s.gpr .r5).toNat = c16) (hc16 : c16 ≤ 38)
    (hl : VG.Proof.X25519.Arm.Lim s.mem (State.addr b) o) :
    WP isa (.block (tail o)) s fun s' =>
      Rest [.r2, .r3, .r4, .r5] s s' ∧ Frame [⟨State.addr b + BitVec.ofNat 64 o, 64⟩] s.mem s'.mem ∧
      VG.Proof.X25519.Arm.Lim s'.mem (State.addr b) o ∧
      VG.Proof.X25519.Arm.V s'.mem (State.addr b) o % P = (VG.Proof.X25519.Arm.V s.mem (State.addr b) o + 2 ^ 256 * c16) % P := by
  have B0 : State.addr (s.gpr .r0) = State.addr b := by rw [hc.r0]
  have t38 : (38 : BitVec 32).toNat = 38 := rfl
  simp only [tail, List.cons_append, List.nil_append]
  refine wp_mul fun s1 u1 => ?_
  have e1 : (s1.gpr .r5).toNat = 38 * c16 := by
    rw [u1.gpr, h8, toNat_mul_lt (by rw [h5, t38]; omega), h5, t38]; omega
  have hc1 : VG.Proof.X25519.Arm.CtxN e b s1 := hc.of_rest (u1.rest (ws := [.r5]) (by decide)) (by decide)
  refine WP.append (VG.Proof.X25519.Arm.pass_ok (s0 := s1) (c := VG.Proof.X25519.Arm.limb s.mem (State.addr b) o) (cin := 38 * c16)
    (by decide) ho (by rw [hc1.r0]; have := hc.fit; omega)
    (fun k hk => by rw [hc1.r0]; exact hc1.inW (by omega))
    (by rw [u1.other _ (by decide), h6]) e1 (fun k hk => by have := hl k hk; omega) (by omega)
    (fun k hk s' hp => WP.mono (VG.Proof.X25519.Arm.ldSrc_ok (hc1.of_rest hp.rest (by decide)) (by omega)) fun s'' h => ?_))
    fun s2 hp => ?_
  · refine ⟨?_, h.2.1.mono (by decide), h.2.2⟩
    rw [h.1, ← u1.mem]
    refine wd_frame hp.frame fun r hr => ?_
    rw [List.mem_singleton.mp hr, hc1.r0]
    exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
  · have hc2 : VG.Proof.X25519.Arm.CtxN e b s2 := hc1.of_rest hp.rest (by decide)
    have ht := tail_facts hl hc16
    have hpo : ∀ j < 16, wd s2.mem (State.addr b) (o + 4 * j) =
        VG.Proof.X25519.Arm.out (VG.Proof.X25519.Arm.limb s.mem (State.addr b) o) (38 * c16) j := fun j hj => by
      have := hp.outs j hj; rwa [hc1.r0] at this
    have hpf : Frame [⟨State.addr b + BitVec.ofNat 64 o, 4 * 16⟩] s1.mem s2.mem := by
      have := hp.frame; rwa [hc1.r0] at this
    refine wp_mul fun s3 u3 => ?_
    have e3 : (s3.gpr .r5).toNat = 38 * chain (VG.Proof.X25519.Arm.limb s.mem (State.addr b) o) (38 * c16) 16 := by
      rw [u3.gpr, hp.rest.gpr .r8 (by decide), u1.other .r8 (by decide), h8,
        toNat_mul_lt (by rw [hp.r5, t38]; have := ht.1; omega), hp.r5, t38]; omega
    have hc3 : VG.Proof.X25519.Arm.CtxN e b s3 := hc2.of_rest (u3.rest (ws := [.r5]) (by decide)) (by decide)
    refine VG.Proof.X25519.Arm.ldr0_ok hc3 (by omega) fun s4 u4 => ?_
    refine wp_dp (op2_reg _ _) fun s5 u5 => ?_
    have hc5 : VG.Proof.X25519.Arm.CtxN e b s5 :=
      hc3.of_rest ((u4.rest (ws := [.r3]) (by decide)).trans (u5.rest (by decide))) (by decide)
    refine VG.Proof.X25519.Arm.str0_ok hc5 (by omega) fun s6 u6 => WP.block_nil ?_
    have w0 : s3.mem.readW (State.addr b + BitVec.ofNat 64 o) 32 =
        s2.mem.readW (State.addr b + BitVec.ofNat 64 o) 32 := by
      rw [u3.mem]
    have e5 : (s5.gpr .r3).toNat = tailL (VG.Proof.X25519.Arm.limb s.mem (State.addr b) o) c16 0 := by
      rw [u5.gpr]
      show (s4.gpr .r3 + s4.gpr .r5).toNat = _
      rw [u4.gpr, u4.other .r5 (by decide), w0]
      have o0 := hpo 0 (by decide)
      rw [Nat.mul_zero, Nat.add_zero] at o0
      have h0 := ht.2.1 0 (by decide)
      simp only [tailL, ite_true] at h0 ⊢
      rw [toNat_add_lt (by rw [e3]; unfold wd at o0; rw [o0]; omega), e3]
      unfold wd at o0; rw [o0]
    have hm6 : s6.mem = s2.mem.writeW (State.addr b + BitVec.ofNat 64 o) (s5.gpr .r3) := by
      rw [u6.mem, u5.mem, u4.mem, u3.mem]
    have hlimb : ∀ k < 16, VG.Proof.X25519.Arm.limb s6.mem (State.addr b) o k = tailL (VG.Proof.X25519.Arm.limb s.mem (State.addr b) o) c16 k := by
      intro k hk
      rw [VG.Proof.X25519.Arm.limb, hm6]
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · rw [Nat.mul_zero, Nat.add_zero, wd_write_self, e5]
      · rw [wd_write_other _ _ _ (by omega) (by omega) (by omega), hpo k hk]
        simp only [tailL, show k ≠ 0 by omega, ite_false]
    refine ⟨?_, ?_, fun k hk => by rw [hlimb k hk]; exact ht.2.1 k hk, ?_⟩
    · refine (u1.rest (ws := [.r2, .r3, .r4, .r5]) (by decide)).trans (hp.rest.trans ?_)
      refine (u3.rest (by decide)).trans ((u4.rest (by decide)).trans ((u5.rest (by decide)).trans ?_))
      exact u6.rest _
    · rw [hm6]
      refine (?_ : Frame _ s.mem s2.mem).writeW (List.mem_singleton_self _) _
        (Offset.contains (State.addr b) (d := o) (n := 4) (e := o) (k := 64) (Nat.le_refl _)
          (by omega) (by omega))
      rw [← u1.mem]
      exact hpf
    · rw [VG.Proof.X25519.Arm.V, val16_congr hlimb, ht.2.2]; rfl

end

end VG.Proof.X25519.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.Arm.AddSub`. -/
section

/-!
# X25519 on 32-bit ARM: sums and differences

`add o x y` and `sub o x y` store at `o` a number congruent to `[x] + [y]` and
`[x] - [y]` (as `[x] + 4p - [y]`), with limbs below `2¹⁶`; `o` may be `x` or
`y`.
-/

namespace VG.Proof.X25519.Arm

open VG VG.Arm VG.Impl.X25519.Arm
open VG.Spec.X25519 (P)

section
variable {e : Nat} {b : BitVec 32}

/-- A word the pass has not written yet (the pass writes `[o, o + 4k)`). -/
theorem wd_pass {s0 s : State} (hc : VG.Proof.X25519.Arm.CtxN e b s0) {o k d : Nat}
    (hf : Frame [⟨State.addr (s0.gpr .r0) + BitVec.ofNat 64 o, 4 * k⟩] s0.mem s.mem)
    (hd : d + 4 ≤ o ∨ o + 4 * k ≤ d) (hd' : d + 4 ≤ 4096) (ho : o + 4 * k ≤ 4096) :
    wd s.mem (State.addr b) d = wd s0.mem (State.addr b) d := by
  rw [hc.r0] at hf
  exact wd_frame hf fun r hr => by
    rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ hd (by omega) (by omega)

theorem subK : ∀ k < 16, encodable (subHi k) = true ∧ encodable (subLo k) = true ∧
    (subLo k).toNat ≤ (subHi k).toNat ∧ (subHi k).toNat - (subLo k).toNat = fourP k ∧
    (subHi k).toNat ≤ 262144 := by decide

/-- A `pass` of sums, then the `tail`, with the mask in `r6`, 38 in `r8` and no
carry in `r5`. -/
theorem passTail'_ok {o : Nat} (ho : o + 64 ≤ 4096) {src : Nat → List Instr} {c : Nat → Nat}
    (hc : ∀ k < 16, c k + 65536 ≤ 2 ^ 32) (hv : val16 c 16 < 39 * 2 ^ 256) {s1 : State}
    (hc1 : VG.Proof.X25519.Arm.CtxN e b s1) (h6 : s1.gpr .r6 = mask16) (h8 : s1.gpr .r8 = 38) (h5 : s1.gpr .r5 = 0)
    (hsrc : ∀ k < 16, ∀ s', VG.Proof.X25519.Arm.PassInv .r0 o s1 c 0 k s' → WP isa (.block (src k)) s' fun s'' =>
        (s''.gpr .r3).toNat = c k ∧ Rest [.r2, .r3, .r4] s' s'' ∧ s''.mem = s'.mem) :
    WP isa (.block (pass .r0 o src ++ tail o)) s1 fun s' =>
      Rest [.r2, .r3, .r4, .r5] s1 s' ∧ Frame [⟨State.addr b + BitVec.ofNat 64 o, 64⟩] s1.mem s'.mem ∧
      VG.Proof.X25519.Arm.Lim s'.mem (State.addr b) o ∧ VG.Proof.X25519.Arm.V s'.mem (State.addr b) o % P = val16 c 16 % P := by
  refine WP.append (VG.Proof.X25519.Arm.pass_ok (s0 := s1) (c := c) (cin := 0) (by decide) ho
    (by rw [hc1.r0]; have := hc1.fit; omega) (fun k hk => by rw [hc1.r0]; exact hc1.inW (by omega))
    h6 (by rw [h5]; rfl) hc (by decide) hsrc) fun s2 hp => ?_
  have hc2 : VG.Proof.X25519.Arm.CtxN e b s2 := hc1.of_rest hp.rest (by decide)
  have hpo : ∀ j < 16, wd s2.mem (State.addr b) (o + 4 * j) = VG.Proof.X25519.Arm.out c 0 j := fun j hj => by
    have := hp.outs j hj; rwa [hc1.r0] at this
  have hpf : Frame [⟨State.addr b + BitVec.ofNat 64 o, 64⟩] s1.mem s2.mem := by
    have := hp.frame; rwa [hc1.r0] at this
  have hcl := carry_le hv
  have hl2 : VG.Proof.X25519.Arm.Lim s2.mem (State.addr b) o := fun k hk => by rw [VG.Proof.X25519.Arm.limb, hpo k hk]; exact out_lt _ _ _
  refine WP.mono (VG.Proof.X25519.Arm.tail_ok ho hc2 (by rw [hp.rest.gpr _ (by decide), h6])
    (by rw [hp.rest.gpr _ (by decide), h8]) hp.r5 hcl hl2) fun s3 ⟨hr3, hf3, hl3, hv3⟩ => ?_
  refine ⟨hp.rest.trans hr3, hpf.trans hf3, hl3, ?_⟩
  rw [hv3, VG.Proof.X25519.Arm.V, val16_congr (f := VG.Proof.X25519.Arm.limb s2.mem (State.addr b) o) (g := VG.Proof.X25519.Arm.out c 0) (fun k hk => hpo k hk),
    chain_val, Nat.add_zero]

/-- The operations built from a `pass` of sums and the `tail`. -/
theorem passTail_ok {o : Nat} (ho : o + 64 ≤ 4096) {src : Nat → List Instr} {c : Nat → Nat}
    (hc : ∀ k < 16, c k + 65536 ≤ 2 ^ 32) (hv : val16 c 16 < 39 * 2 ^ 256) {s : State}
    (hctx : VG.Proof.X25519.Arm.CtxN e b s)
    (hsrc : ∀ s1 : State, VG.Proof.X25519.Arm.CtxN e b s1 → Rest VG.Proof.X25519.Arm.clob s s1 → s1.mem = s.mem → ∀ k < 16, ∀ s',
      VG.Proof.X25519.Arm.PassInv .r0 o s1 c 0 k s' → WP isa (.block (src k)) s' fun s'' =>
        (s''.gpr .r3).toNat = c k ∧ Rest [.r2, .r3, .r4] s' s'' ∧ s''.mem = s'.mem) :
    WP isa (.block (prologue ++ pass .r0 o src ++ tail o)) s fun s' =>
      Rest VG.Proof.X25519.Arm.clob s s' ∧ Frame [⟨State.addr b + BitVec.ofNat 64 o, 64⟩] s.mem s'.mem ∧
      VG.Proof.X25519.Arm.Lim s'.mem (State.addr b) o ∧ VG.Proof.X25519.Arm.V s'.mem (State.addr b) o % P = val16 c 16 % P := by
  rw [List.append_assoc]
  refine WP.append VG.Proof.X25519.Arm.prologue_ok fun s1 ⟨h6, h8, h5, hr1, hm1⟩ => ?_
  have hc1 : VG.Proof.X25519.Arm.CtxN e b s1 := hctx.of_rest hr1 (by decide)
  refine WP.mono (VG.Proof.X25519.Arm.passTail'_ok ho hc hv hc1 h6 h8 h5 (hsrc s1 hc1 (hr1.mono (by decide)) hm1))
    fun s3 ⟨hr3, hf3, hl3, hv3⟩ => ⟨(hr1.mono (by decide)).trans (hr3.mono (by decide)),
      by rw [← hm1]; exact hf3, hl3, hv3⟩

theorem add_ok {o x y : Nat} (ho : o + 64 ≤ 4096) (hx : x + 64 ≤ 4096) (hy : y + 64 ≤ 4096)
    (hox : o = x ∨ o + 64 ≤ x ∨ x + 64 ≤ o) (hoy : o = y ∨ o + 64 ≤ y ∨ y + 64 ≤ o)
    {s : State} (hc : VG.Proof.X25519.Arm.CtxN e b s) (hlx : VG.Proof.X25519.Arm.Lim s.mem (State.addr b) x) (hly : VG.Proof.X25519.Arm.Lim s.mem (State.addr b) y) :
    WP isa (.block (add o x y)) s fun s' =>
      Rest VG.Proof.X25519.Arm.clob s s' ∧ Frame [⟨State.addr b + BitVec.ofNat 64 o, 64⟩] s.mem s'.mem ∧
      VG.Proof.X25519.Arm.Lim s'.mem (State.addr b) o ∧
      VG.Proof.X25519.Arm.V s'.mem (State.addr b) o % P = (VG.Proof.X25519.Arm.V s.mem (State.addr b) x + VG.Proof.X25519.Arm.V s.mem (State.addr b) y) % P := by
  have hvx := VG.Proof.X25519.Arm.V_lt hlx
  have hvy := VG.Proof.X25519.Arm.V_lt hly
  refine WP.mono (VG.Proof.X25519.Arm.passTail_ok (c := fun k => VG.Proof.X25519.Arm.limb s.mem (State.addr b) x k + VG.Proof.X25519.Arm.limb s.mem (State.addr b) y k)
    ho (fun k hk => by have := hlx k hk; have := hly k hk; omega)
    (by rw [val16_add]; exact Nat.lt_of_lt_of_le (Nat.add_lt_add hvx hvy) (by omega)) hc ?_)
    fun s' ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, by rw [h4, val16_add]; rfl⟩
  intro s1 hc1 _ hm1 k hk s' hp
  have hc' : VG.Proof.X25519.Arm.CtxN e b s' := hc1.of_rest hp.rest (by decide)
  refine VG.Proof.X25519.Arm.ldr0_ok hc' (d := x + 4 * k) (by omega) fun t1 v1 => ?_
  have hc1' : VG.Proof.X25519.Arm.CtxN e b t1 := hc'.of_rest (v1.rest (ws := [.r3]) (by decide)) (by decide)
  refine VG.Proof.X25519.Arm.ldr0_ok hc1' (d := y + 4 * k) (by omega) fun t2 v2 => ?_
  refine wp_dp (op2_reg _ _) fun t3 v3 => WP.block_nil ⟨?_, ?_, by rw [v3.mem, v2.mem, v1.mem]⟩
  · have ex : wd s'.mem (State.addr b) (x + 4 * k) = VG.Proof.X25519.Arm.limb s.mem (State.addr b) x k := by
      rw [VG.Proof.X25519.Arm.wd_pass hc1 hp.frame (by omega) (by omega) (by omega), hm1]; rfl
    have ey : wd t1.mem (State.addr b) (y + 4 * k) = VG.Proof.X25519.Arm.limb s.mem (State.addr b) y k := by
      rw [v1.mem, VG.Proof.X25519.Arm.wd_pass hc1 hp.frame (by omega) (by omega) (by omega), hm1]; rfl
    have := hlx k hk; have := hly k hk
    rw [v3.gpr]
    show (t2.gpr .r3 + t2.gpr .r2).toNat = _
    rw [v2.other .r3 (by decide), v1.gpr, v2.gpr]
    unfold wd at ex ey
    rw [toNat_add_lt (by rw [ex, ey]; omega), ex, ey]
  · exact (v1.rest (by decide)).trans ((v2.rest (by decide)).trans (v3.rest (by decide)))

theorem sub_ok {o x y : Nat} (ho : o + 64 ≤ 4096) (hx : x + 64 ≤ 4096) (hy : y + 64 ≤ 4096)
    (hox : o = x ∨ o + 64 ≤ x ∨ x + 64 ≤ o) (hoy : o = y ∨ o + 64 ≤ y ∨ y + 64 ≤ o)
    {s : State} (hc : VG.Proof.X25519.Arm.CtxN e b s) (hlx : VG.Proof.X25519.Arm.Lim s.mem (State.addr b) x) (hly : VG.Proof.X25519.Arm.Lim s.mem (State.addr b) y) :
    WP isa (.block (sub o x y)) s fun s' =>
      Rest VG.Proof.X25519.Arm.clob s s' ∧ Frame [⟨State.addr b + BitVec.ofNat 64 o, 64⟩] s.mem s'.mem ∧
      VG.Proof.X25519.Arm.Lim s'.mem (State.addr b) o ∧
      (VG.Proof.X25519.Arm.V s'.mem (State.addr b) o + VG.Proof.X25519.Arm.V s.mem (State.addr b) y) % P = VG.Proof.X25519.Arm.V s.mem (State.addr b) x % P := by
  have hvx := VG.Proof.X25519.Arm.V_lt hlx
  have hvy := VG.Proof.X25519.Arm.V_lt hly
  obtain ⟨hcb, hcv⟩ := subC_facts hlx hly
  have hPv : 4 * P < 2 * 2 ^ 256 := by decide
  change val16 _ 16 + VG.Proof.X25519.Arm.V s.mem (State.addr b) y = VG.Proof.X25519.Arm.V s.mem (State.addr b) x + 4 * P at hcv
  refine WP.mono (VG.Proof.X25519.Arm.passTail_ok (c := subC (VG.Proof.X25519.Arm.limb s.mem (State.addr b) x) (VG.Proof.X25519.Arm.limb s.mem (State.addr b) y))
    ho hcb (by omega) hc ?_) fun s' ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, by
      rw [Nat.add_mod, h4, ← Nat.add_mod, hcv, Nat.mul_comm, Nat.add_mul_mod_self_left]⟩
  intro s1 hc1 _ hm1 k hk s' hp
  have hc' : VG.Proof.X25519.Arm.CtxN e b s' := hc1.of_rest hp.rest (by decide)
  obtain ⟨e1, e2, e3, e4, e5⟩ := VG.Proof.X25519.Arm.subK k hk
  have ex : wd s'.mem (State.addr b) (x + 4 * k) = VG.Proof.X25519.Arm.limb s.mem (State.addr b) x k := by
    rw [VG.Proof.X25519.Arm.wd_pass hc1 hp.frame (by omega) (by omega) (by omega), hm1]; rfl
  have hX := hlx k hk
  have hY := hly k hk
  have hK := fourP_ge k hk
  refine VG.Proof.X25519.Arm.ldr0_ok hc' (d := x + 4 * k) (by omega) fun t1 v1 => ?_
  refine wp_dp (op2_imm e1) fun t2 v2 => wp_dp (op2_imm e2) fun t3 v3 => ?_
  have hc3 : VG.Proof.X25519.Arm.CtxN e b t3 :=
    hc'.of_rest ((v1.rest (ws := [.r3]) (by decide)).trans ((v2.rest (by decide)).trans
      (v3.rest (by decide)))) (by decide)
  refine VG.Proof.X25519.Arm.ldr0_ok hc3 (d := y + 4 * k) (by omega) fun t4 v4 => ?_
  refine wp_dp (op2_reg _ _) fun t5 v5 => WP.block_nil ⟨?_, ?_, by
    rw [v5.mem, v4.mem, v3.mem, v2.mem, v1.mem]⟩
  · have ey : wd t3.mem (State.addr b) (y + 4 * k) = VG.Proof.X25519.Arm.limb s.mem (State.addr b) y k := by
      rw [v3.mem, v2.mem, v1.mem, VG.Proof.X25519.Arm.wd_pass hc1 hp.frame (by omega) (by omega) (by omega), hm1]; rfl
    unfold wd at ex ey
    have r1 : (t1.gpr .r3).toNat = VG.Proof.X25519.Arm.limb s.mem (State.addr b) x k := by rw [v1.gpr, ex]
    have r2 : (t2.gpr .r3).toNat = VG.Proof.X25519.Arm.limb s.mem (State.addr b) x k + (subHi k).toNat := by
      rw [v2.gpr]; show (t1.gpr .r3 + subHi k).toNat = _
      rw [toNat_add_lt (by rw [r1]; omega), r1]
    have r3 : (t3.gpr .r3).toNat = VG.Proof.X25519.Arm.limb s.mem (State.addr b) x k + fourP k := by
      rw [v3.gpr]; show (t2.gpr .r3 - subLo k).toNat = _
      rw [toNat_sub_le (by rw [r2]; omega), r2]; omega
    rw [v5.gpr]
    show (t4.gpr .r3 - t4.gpr .r2).toNat = _
    rw [v4.other .r3 (by decide), v4.gpr, toNat_sub_le (by rw [r3, ey]; omega), r3, ey]; rfl
  · exact (v1.rest (by decide)).trans ((v2.rest (by decide)).trans ((v3.rest (by decide)).trans
      ((v4.rest (by decide)).trans (v5.rest (by decide)))))

end

end VG.Proof.X25519.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.Arm.Mul`. -/
section

/-!
# X25519 on 32-bit ARM: multiplication

`mulAt acc o x y` computes the 32 limbs of `[x] · [y]` at `acc`, row by row
(`row_ok`, the loop invariant `RowInv`: after `i` rows, `acc[0, i + 16)` holds
the limbs of `x_{<i} · y`), then stores at `o` a number congruent to it, with
limbs below `2¹⁶` (`mul_ok`), for any `acc` an offset reaches: X25519's
`ACC` and Ed25519's.
-/

namespace VG.Proof.X25519.Arm

open VG VG.Arm VG.Impl.X25519.Arm
open VG.Spec.X25519 (P)

/-- Limb `k` of the product at `acc`. -/
def accw (acc : Nat) (m : Mem) (B : Addr) (k : Nat) : Nat := wd m B (acc + 4 * k)

theorem wd_shift (m : Mem) (B : Addr) (a d : Nat) : wd m (B + BitVec.ofNat 64 a) d = wd m B (a + d) := by
  unfold wd; rw [Offset.add_add]

theorem ACC_eq : ACC = 1152 := rfl

section
variable {e acc : Nat} {b : BitVec 32}

theorem addr7 (hfit : b.toNat + 4096 ≤ 2 ^ 32) {i : Nat} (hi : 4 * i < 4096) :
    State.addr (b + BitVec.ofNat 32 (4 * i)) = State.addr b + BitVec.ofNat 64 (4 * i) :=
  addr_add (by omega)

theorem toNat7 (hfit : b.toNat + 4096 ≤ 2 ^ 32) {i : Nat} (hi : 4 * i < 4096) :
    (b + BitVec.ofNat 32 (4 * i)).toNat = b.toNat + 4 * i := by
  rw [toNat_add_lt (by rw [toNat_imm (by omega)]; omega), toNat_imm (by omega)]

theorem ea7 (hfit : b.toNat + 4096 ≤ 2 ^ 32) {i d : Nat} (h : 4 * i + d < 4096) :
    State.addr (b + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 d) =
      State.addr b + BitVec.ofNat 64 (4 * i + d) := by
  rw [Offset.add_add]; exact addr_add (by omega)

theorem zeroAcc_ok (hA : acc + 128 ≤ 4096) {s : State} (hc : VG.Proof.X25519.Arm.CtxN e b s) :
    WP isa (.block (zeroAcc acc)) s fun s' => (∀ j < 16, VG.Proof.X25519.Arm.accw acc s'.mem (State.addr b) j = 0) ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 acc, 64⟩] s.mem s'.mem ∧ Rest [.r3] s s' := by
  unfold zeroAcc storeN
  refine wp_mov (op2_imm (by decide)) fun s1 u1 => ?_
  have hc1 := hc.of_rest (u1.rest (ws := [.r3]) (by decide)) (by decide)
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun n s' => (∀ j < n, VG.Proof.X25519.Arm.accw acc s'.mem (State.addr b) j = 0) ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 acc, 64⟩] s1.mem s'.mem ∧ Rest [] s1 s' ∧ s'.gpr .r3 = 0)
    (fun n s' hn ⟨h1, h2, h3, h4⟩ => ?_) 16 (Nat.le_refl _) s1
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), Frame.refl _ _, Rest.refl _ _, u1.gpr⟩)
    fun s' ⟨h1, h2, h3, _⟩ => ⟨h1, by rw [← u1.mem]; exact h2,
      (u1.rest (by decide)).trans (h3.mono (by decide))⟩
  refine VG.Proof.X25519.Arm.str0_ok (hc1.of_rest h3 (by decide)) (d := acc + 4 * n) (by omega) fun s2 u2 =>
    WP.block_nil ⟨fun j hj => ?_, ?_, h3.trans (u2.rest _), by rw [u2.gpr, h4]⟩
  · rw [VG.Proof.X25519.Arm.accw, u2.mem]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [wd_write_other _ _ _ (by omega) (by omega) (by omega)]; exact h1 j hj
    · rw [wd_write_self, h4]; rfl
  · rw [u2.mem]
    exact h2.writeW (List.mem_singleton_self _) _ (Offset.contains _ (by omega) (by omega) (by omega))

/-- The loop invariant of the rows of `mul o x y` from `s0`, after `i` rows. -/
structure RowInv (e acc : Nat) (b : BitVec 32) (x y : Nat) (s0 : State) (i : Nat) (s : State) : Prop where
  ctx : VG.Proof.X25519.Arm.CtxN e b s
  rest : Rest VG.Proof.X25519.Arm.clob s0 s
  r6 : s.gpr .r6 = mask16
  r8 : s.gpr .r8 = 38
  r7 : s.gpr .r7 = b + BitVec.ofNat 32 (4 * i)
  r9 : s.gpr .r9 = BitVec.ofNat 32 (16 - i)
  frame : Frame [⟨State.addr b + BitVec.ofNat 64 acc, 128⟩] s0.mem s.mem
  lt : ∀ k < i + 16, VG.Proof.X25519.Arm.accw acc s.mem (State.addr b) k < 65536
  val : val16 (VG.Proof.X25519.Arm.accw acc s.mem (State.addr b)) (i + 16) =
    val16 (VG.Proof.X25519.Arm.limb s0.mem (State.addr b) x) i * VG.Proof.X25519.Arm.V s0.mem (State.addr b) y

theorem mulPre_ok (hA : acc + 128 ≤ 4096) {x y : Nat} {s : State} (hc : VG.Proof.X25519.Arm.CtxN e b s) :
    WP isa (.block (prologue ++ zeroAcc acc ++ ([.mov .r7 (.reg .r0), .mov .r9 (.imm 16)] : List Instr))) s
      (VG.Proof.X25519.Arm.RowInv e acc b x y s 0) := by
  rw [List.append_assoc]
  refine WP.append VG.Proof.X25519.Arm.prologue_ok fun s1 ⟨h6, h8, h5, hr1, hm1⟩ => ?_
  have hc1 : VG.Proof.X25519.Arm.CtxN e b s1 := hc.of_rest hr1 (by decide)
  refine WP.append (VG.Proof.X25519.Arm.zeroAcc_ok hA hc1) fun s2 ⟨hz, hf2, hr2⟩ => ?_
  have hc2 : VG.Proof.X25519.Arm.CtxN e b s2 := hc1.of_rest hr2 (by decide)
  refine wp_mov (op2_reg _ _) fun s3 u3 => wp_mov (op2_imm (by decide)) fun s4 u4 => WP.block_nil ?_
  have hr : Rest VG.Proof.X25519.Arm.clob s s4 :=
    (hr1.mono (by decide)).trans ((hr2.mono (by decide)).trans ((u3.rest (by decide)).trans
      (u4.rest (by decide))))
  have hr' : Rest [.r3, .r7, .r9] s1 s4 :=
    (hr2.mono (by decide)).trans ((u3.rest (by decide)).trans (u4.rest (by decide)))
  have hm4 : s4.mem = s2.mem := by rw [u4.mem, u3.mem]
  refine ⟨hc.of_rest hr (by decide), hr, by rw [hr'.gpr _ (by decide), h6],
    by rw [hr'.gpr _ (by decide), h8], ?_, u4.gpr, ?_, fun k hk => ?_, ?_⟩
  · rw [u4.other _ (by decide), u3.gpr, hc2.r0]; exact (BitVec.add_zero b).symm
  · rw [hm4, ← hm1]; exact hf2.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by decide)⟩
  · rw [VG.Proof.X25519.Arm.accw, hm4]; unfold VG.Proof.X25519.Arm.accw at hz; rw [hz k (by omega)]; decide
  · rw [hm4, val16_congr (g := fun _ => 0) (fun k hk => hz k hk), val16_zero_fn]
    exact (Nat.zero_mul _).symm

theorem row_ok (hA : acc + 128 ≤ 4096) {x y : Nat} (hx : x + 64 ≤ acc) (hy : y + 64 ≤ acc)
    {s0 : State} (hlx : VG.Proof.X25519.Arm.Lim s0.mem (State.addr b) x) (hly : VG.Proof.X25519.Arm.Lim s0.mem (State.addr b) y) {i : Nat}
    (hi : i < 16) {s : State} (h : VG.Proof.X25519.Arm.RowInv e acc b x y s0 i s) :
    WP isa (.block (row acc x y)) s fun s' =>
      VG.Proof.X25519.Arm.RowInv e acc b x y s0 (i + 1) s' ∧ s'.z = decide (16 - (i + 1) = 0) := by
  have hfit : b.toNat + 4096 ≤ 2 ^ 32 := by have := h.ctx.fit; omega
  have hframe0 : ∀ z : Nat, z + 64 ≤ acc → ∀ k < 16,
      VG.Proof.X25519.Arm.limb s.mem (State.addr b) z k = VG.Proof.X25519.Arm.limb s0.mem (State.addr b) z k := fun z hz k hk =>
    wd_frame h.frame fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
  simp only [row, List.cons_append, List.nil_append]
  refine wp_ldr (a := State.addr b + BitVec.ofNat 64 (x + 4 * i)) (by omega)
    (by rw [h.r7, VG.Proof.X25519.Arm.ea7 hfit (by omega), Nat.add_comm]) (h.ctx.inR (by omega)) fun s1 u1 => ?_
  refine wp_mov (op2_imm (by decide)) fun s2 u2 => ?_
  have hr2 : Rest [.r1, .r5] s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  have hc2 : VG.Proof.X25519.Arm.CtxN e b s2 := h.ctx.of_rest hr2 (by decide)
  have hm2 : s2.mem = s.mem := by rw [u2.mem, u1.mem]
  have e1 : (s2.gpr .r1).toNat = VG.Proof.X25519.Arm.limb s0.mem (State.addr b) x i := by
    rw [u2.other _ (by decide), u1.gpr, ← hframe0 x hx i hi]; rfl
  have e7 : s2.gpr .r7 = b + BitVec.ofNat 32 (4 * i) := by rw [hr2.gpr _ (by decide), h.r7]
  have P7 : State.addr (s2.gpr .r7) = State.addr b + BitVec.ofNat 64 (4 * i) := by
    rw [e7]; exact VG.Proof.X25519.Arm.addr7 hfit (by omega)
  have hlt : ∀ j < 16, rowC (VG.Proof.X25519.Arm.accw acc s.mem (State.addr b)) (VG.Proof.X25519.Arm.limb s0.mem (State.addr b) x)
      (VG.Proof.X25519.Arm.limb s0.mem (State.addr b) y) i j + 65536 ≤ 2 ^ 32 := fun j hj =>
    rowC_le (hlx i hi) (hly j hj) (h.lt (i + j) (by omega))
  refine WP.append (VG.Proof.X25519.Arm.pass_ok (rb := .r7) (o := acc) (s0 := s2)
    (c := rowC (VG.Proof.X25519.Arm.accw acc s.mem (State.addr b)) (VG.Proof.X25519.Arm.limb s0.mem (State.addr b) x) (VG.Proof.X25519.Arm.limb s0.mem (State.addr b) y) i)
    (cin := 0) (by decide) (by omega) (by rw [e7, VG.Proof.X25519.Arm.toNat7 hfit (by omega)]; omega)
    (fun k hk => by rw [P7, Offset.add_add]; exact hc2.inW (by omega))
    (by rw [hr2.gpr _ (by decide), h.r6]) (by rw [u2.gpr]; rfl) hlt (by decide) ?_) fun s3 hp => ?_
  · -- The sums of the row.
    intro k hk s' hp'
    have hc' : VG.Proof.X25519.Arm.CtxN e b s' := hc2.of_rest hp'.rest (by decide)
    have hf' : Frame [⟨State.addr b + BitVec.ofNat 64 (4 * i + acc), 4 * k⟩] s2.mem s'.mem := by
      have := hp'.frame; rwa [P7, Offset.add_add] at this
    simp only [rowSrc]
    refine VG.Proof.X25519.Arm.ldr0_ok hc' (d := y + 4 * k) (by omega) fun t1 v1 => ?_
    refine wp_mul fun t2 v2 => ?_
    refine wp_ldr (a := State.addr b + BitVec.ofNat 64 (4 * i + (acc + 4 * k))) (by omega)
      (by rw [v2.other _ (by decide), v1.other _ (by decide), hp'.rest.gpr _ (by decide), e7,
        VG.Proof.X25519.Arm.ea7 hfit (by omega)]) (by rw [v2.rd, v2.wr, v1.rd, v1.wr]; exact hc'.inR (by omega))
      fun t3 v3 => ?_
    refine wp_dp (op2_reg _ _) fun t4 v4 => WP.block_nil ⟨?_, ?_, by
      rw [v4.mem, v3.mem, v2.mem, v1.mem]⟩
    · have ey : (t1.gpr .r2).toNat = VG.Proof.X25519.Arm.limb s0.mem (State.addr b) y k := by
        rw [v1.gpr, ← hframe0 y hy k hk, ← hm2]
        show wd s'.mem _ _ = wd s2.mem _ _
        exact wd_frame hf' fun r hr => by
          rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
      have ea : (t1.gpr .r1).toNat = VG.Proof.X25519.Arm.limb s0.mem (State.addr b) x i := by
        rw [v1.other _ (by decide), hp'.rest.gpr _ (by decide), e1]
      have hab := Nat.mul_le_mul (Nat.le_of_lt_succ (hlx i hi)) (Nat.le_of_lt_succ (hly k hk))
      have e2 : (t2.gpr .r2).toNat = VG.Proof.X25519.Arm.limb s0.mem (State.addr b) x i * VG.Proof.X25519.Arm.limb s0.mem (State.addr b) y k := by
        rw [v2.gpr, toNat_mul_lt (by rw [ea, ey]; omega), ea, ey]
      have e3 : (t3.gpr .r3).toNat = VG.Proof.X25519.Arm.accw acc s.mem (State.addr b) (i + k) := by
        rw [v3.gpr, v2.mem, v1.mem, VG.Proof.X25519.Arm.accw, ← hm2]
        show wd s'.mem _ _ = _
        rw [wd_frame hf' fun r hr => by
          rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)]
        congr 1; omega
      have := hlt k hk
      rw [v4.gpr]
      show (t3.gpr .r3 + t3.gpr .r2).toNat = _
      rw [v3.other .r2 (by decide), toNat_add_lt (by rw [e3, e2]; simp only [rowC] at this; omega), e3, e2,
        rowC, Nat.add_comm]
    · exact (v1.rest (by decide)).trans ((v2.rest (by decide)).trans ((v3.rest (by decide)).trans
        (v4.rest (by decide))))
  · -- The carry, and the next row.
    have hc3 : VG.Proof.X25519.Arm.CtxN e b s3 := hc2.of_rest hp.rest (by decide)
    have e7' : s3.gpr .r7 = b + BitVec.ofNat 32 (4 * i) := by rw [hp.rest.gpr _ (by decide), e7]
    refine wp_str (a := State.addr b + BitVec.ofNat 64 (4 * i + (acc + 64))) (by omega)
      (by rw [e7', VG.Proof.X25519.Arm.ea7 hfit (by omega)]) (hc3.inW (by omega)) fun s4 u4 => ?_
    refine wp_dp (op2_imm (by decide)) fun s5 u5 => wp_subs (op2_imm (by decide)) fun s6 u6 hz => ?_
    refine WP.block_nil ?_
    have hr6 : Rest [.r1, .r2, .r3, .r4, .r5, .r7, .r9] s s6 :=
      (hr2.mono (by decide)).trans ((hp.rest.mono (by decide)).trans ((u4.rest _).trans
        ((u5.rest (by decide)).trans (u6.rest (by decide)))))
    have hm6 : s6.mem = s3.mem.writeW (State.addr b + BitVec.ofNat 64 (4 * i + (acc + 64))) (s3.gpr .r5) := by
      rw [u6.mem, u5.mem, u4.mem]
    have hpf : Frame [⟨State.addr b + BitVec.ofNat 64 (4 * i + acc), 64⟩] s.mem s3.mem := by
      have := hp.frame; rw [P7, Offset.add_add] at this; rw [← hm2]; exact this
    have hr9 : s6.gpr .r9 = BitVec.ofNat 32 (16 - (i + 1)) := by
      rw [u6.gpr, u5.other _ (by decide), u4.gpr, hp.rest.gpr _ (by decide), hr2.gpr _ (by decide), h.r9]
      have t1 : (1 : BitVec 32).toNat = 1 := rfl
      apply BitVec.eq_of_toNat_eq
      rw [toNat_sub_le (by rw [toNat_imm (by omega), t1]; omega), toNat_imm (by omega), toNat_imm (by omega),
        t1]
      omega
    -- The limbs of `acc` after the row.
    have hacc : ∀ k < i + 17, VG.Proof.X25519.Arm.accw acc s6.mem (State.addr b) k =
        rowAcc (VG.Proof.X25519.Arm.accw acc s.mem (State.addr b)) (VG.Proof.X25519.Arm.limb s0.mem (State.addr b) x) (VG.Proof.X25519.Arm.limb s0.mem (State.addr b) y) i k := by
      intro k hk
      rw [VG.Proof.X25519.Arm.accw, hm6]
      rcases Nat.lt_or_ge k (i + 16) with hk' | hk'
      · rw [wd_write_other _ _ _ (by omega) (by omega) (by omega)]
        rcases Nat.lt_or_ge k i with hki | hki
        · rw [wd_frame hpf fun r hr => by
            rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)]
          simp only [rowAcc, hki, ite_true]; rfl
        · have := hp.outs (k - i) (by omega)
          rw [P7, VG.Proof.X25519.Arm.wd_shift, show 4 * i + (acc + 4 * (k - i)) = acc + 4 * k by omega] at this
          rw [this]
          simp only [rowAcc, show ¬ k < i by omega, hk', ite_false, ite_true]
      · rw [show acc + 4 * k = 4 * i + (acc + 64) by omega, wd_write_self, hp.r5]
        simp only [rowAcc, show ¬ k < i by omega, show ¬ k < i + 16 by omega, ite_false]
    refine ⟨⟨hc3.of_rest ((u4.rest [.r7, .r9]).trans ((u5.rest (by decide)).trans (u6.rest (by decide))))
        (by decide), h.rest.trans (hr6.mono (by decide)), by rw [hr6.gpr _ (by decide), h.r6],
      by rw [hr6.gpr _ (by decide), h.r8], ?_, hr9, ?_, fun k hk => ?_, ?_⟩, ?_⟩
    · rw [u6.other _ (by decide), u5.gpr, u4.gpr, e7']
      show b + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 4 = _
      rw [Offset.add_add, Nat.mul_succ]
    · rw [hm6]
      refine (h.frame.trans (hpf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)).writeW
        (List.mem_singleton_self _) _ (Offset.contains _ (by omega) (by omega) (by omega))
      rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by omega) (by omega)
    · rw [hacc k hk]
      exact rowAcc_lt (fun k hk => h.lt k (by omega)) hlt k hk
    · rw [val16_congr hacc]; exact row_val h.val
    · rw [hz, ← u6.gpr, hr9, ofNat_beq_zero (by omega)]

theorem mul_ok (hA : acc + 128 ≤ 4096) {o x y : Nat} (ho : o + 64 ≤ acc) (hx : x + 64 ≤ acc)
    (hy : y + 64 ≤ acc) {s : State} (hc : VG.Proof.X25519.Arm.CtxN e b s) (hlx : VG.Proof.X25519.Arm.Lim s.mem (State.addr b) x)
    (hly : VG.Proof.X25519.Arm.Lim s.mem (State.addr b) y) :
    WP isa (mulAt acc o x y) s fun s' =>
      Rest VG.Proof.X25519.Arm.clob s s' ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 o, 64⟩, ⟨State.addr b + BitVec.ofNat 64 acc, 128⟩] s.mem s'.mem ∧
      VG.Proof.X25519.Arm.Lim s'.mem (State.addr b) o ∧
      VG.Proof.X25519.Arm.V s'.mem (State.addr b) o % P = (VG.Proof.X25519.Arm.V s.mem (State.addr b) x * VG.Proof.X25519.Arm.V s.mem (State.addr b) y) % P := by
  unfold mulAt
  refine WP.seq (WP.mono (VG.Proof.X25519.Arm.mulPre_ok hA (x := x) (y := y) hc) fun s1 h1 => ?_)
  refine WP.seq (WP.mono (Q := VG.Proof.X25519.Arm.RowInv e acc b x y s 16) (WP.loop (M := isa)
    (fun n s' => ∃ i, n = 16 - i ∧ i < 16 ∧ VG.Proof.X25519.Arm.RowInv e acc b x y s i s') ?_ 16 s1 ⟨0, rfl, by decide, h1⟩)
    fun s2 h2 => ?_)
  · rintro n s' ⟨i, rfl, hi, hr⟩
    refine WP.mono (VG.Proof.X25519.Arm.row_ok hA hx hy hlx hly hi hr) fun s'' ⟨hr', hz⟩ => ?_
    by_cases h16 : i + 1 = 16
    · refine .inl ⟨by rw [eval_ne, hz]; simp [h16], ?_⟩
      rw [h16] at hr'; exact hr'
    · exact .inr ⟨by rw [eval_ne, hz]; simp; omega, 16 - (i + 1), by omega, i + 1, rfl, by omega, hr'⟩
  · refine wp_mov (op2_imm (by decide)) fun s3 u3 => ?_
    have hc3 : VG.Proof.X25519.Arm.CtxN e b s3 := h2.ctx.of_rest (u3.rest (ws := [.r5]) (by decide)) (by decide)
    have hl32 : ∀ k < 32, VG.Proof.X25519.Arm.accw acc s2.mem (State.addr b) k < 65536 := h2.lt
    have hv : val16 (VG.Proof.X25519.Arm.accw acc s2.mem (State.addr b)) 32 = VG.Proof.X25519.Arm.V s.mem (State.addr b) x * VG.Proof.X25519.Arm.V s.mem (State.addr b) y :=
      h2.val
    have hlo := val16_lt (f := VG.Proof.X25519.Arm.accw acc s2.mem (State.addr b)) (n := 16) fun k hk => hl32 k (by omega)
    have hhi := val16_lt (f := fun k => VG.Proof.X25519.Arm.accw acc s2.mem (State.addr b) (16 + k)) (n := 16) fun k hk =>
      hl32 (16 + k) (by omega)
    have hlox : ∀ z : Nat, z + 64 ≤ acc → ∀ k < 16,
        VG.Proof.X25519.Arm.limb s2.mem (State.addr b) z k = VG.Proof.X25519.Arm.limb s.mem (State.addr b) z k := fun z hz k hk =>
      wd_frame h2.frame fun r hr => by
        rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
    refine WP.mono (VG.Proof.X25519.Arm.passTail'_ok (c := foldC (VG.Proof.X25519.Arm.accw acc s2.mem (State.addr b))) (by omega)
      (foldC_le hl32) (by rw [val16_foldC]; rw [show 16 * 16 = 256 from rfl] at hlo hhi; omega) hc3
      (by rw [u3.other _ (by decide), h2.r6]) (by rw [u3.other _ (by decide), h2.r8]) u3.gpr ?_)
      fun s4 ⟨hr4, hf4, hl4, hv4⟩ => ⟨h2.rest.trans ((u3.rest (by decide)).trans (hr4.mono (by decide))),
        ?_, hl4, ?_⟩
    · intro k hk s' hp
      have hc' : VG.Proof.X25519.Arm.CtxN e b s' := hc3.of_rest hp.rest (by decide)
      refine VG.Proof.X25519.Arm.ldr0_ok hc' (d := acc + 4 * k) (by omega) fun t1 v1 => ?_
      refine VG.Proof.X25519.Arm.ldr0_ok (hc'.of_rest (v1.rest (ws := [.r3]) (by decide)) (by decide)) (d := acc + 64 + 4 * k)
        (by omega) fun t2 v2 => ?_
      refine wp_mul fun t3 v3 => wp_dp (op2_reg _ _) fun t4 v4 => WP.block_nil ⟨?_, ?_, by
        rw [v4.mem, v3.mem, v2.mem, v1.mem]⟩
      · have el : (t1.gpr .r3).toNat = VG.Proof.X25519.Arm.accw acc s2.mem (State.addr b) k := by
          rw [v1.gpr]; show wd s'.mem _ _ = _
          rw [VG.Proof.X25519.Arm.wd_pass hc3 hp.frame (by omega) (by omega) (by omega), u3.mem]; rfl
        have eh : (t2.gpr .r2).toNat = VG.Proof.X25519.Arm.accw acc s2.mem (State.addr b) (16 + k) := by
          rw [v2.gpr, v1.mem]; show wd s'.mem _ _ = _
          rw [VG.Proof.X25519.Arm.wd_pass hc3 hp.frame (by omega) (by omega) (by omega), u3.mem, VG.Proof.X25519.Arm.accw]
          congr 1; omega
        have h8 : t2.gpr .r8 = 38 := by
          rw [v2.other _ (by decide), v1.other _ (by decide), hp.rest.gpr _ (by decide),
            u3.other _ (by decide), h2.r8]
        have hh := hl32 (16 + k) (by omega)
        have hl := hl32 k (by omega)
        have e3 : (t3.gpr .r2).toNat = VG.Proof.X25519.Arm.accw acc s2.mem (State.addr b) (16 + k) * 38 := by
          rw [v3.gpr, h8, toNat_mul_lt (by rw [eh]; show _ * 38 < _; omega), eh]; rfl
        rw [v4.gpr]
        show (t3.gpr .r3 + t3.gpr .r2).toNat = _
        rw [v3.other .r3 (by decide), v2.other .r3 (by decide), toNat_add_lt (by rw [el, e3]; omega), el,
          e3, foldC, Nat.mul_comm]
      · exact (v1.rest (by decide)).trans ((v2.rest (by decide)).trans ((v3.rest (by decide)).trans
          (v4.rest (by decide))))
    · have hf2 : Frame [⟨State.addr b + BitVec.ofNat 64 o, 64⟩, ⟨State.addr b + BitVec.ofNat 64 acc, 128⟩]
          s.mem s2.mem := h2.frame.mono fun r hr => by simp [List.mem_singleton.mp hr]
      rw [u3.mem] at hf4
      exact hf2.trans (hf4.mono fun r hr => by simp [List.mem_singleton.mp hr])
    · rw [hv4, val16_foldC, ← hv, show (32 : Nat) = 16 + 16 from rfl, val16_append, fold256]

end

end VG.Proof.X25519.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.Arm.Cswap`. -/
section

/-!
# X25519 on 32-bit ARM: the conditional swap

`cswap x y` swaps the elements at `x` and `y` if the mask in `r9` is `-1` and
leaves them if it is `0` (`cswap_ok`).
-/

namespace VG.Proof.X25519.Arm

open VG VG.Arm VG.Impl.X25519.Arm

theorem sel0 (a c : BitVec 32) : a ^^^ ((a ^^^ c) &&& (0 - BitVec.ofNat 32 0)) = a := by simp

theorem sel0' (a c : BitVec 32) : c ^^^ ((a ^^^ c) &&& (0 - BitVec.ofNat 32 0)) = c := by simp

theorem sel1 (a c : BitVec 32) : a ^^^ ((a ^^^ c) &&& (0 - BitVec.ofNat 32 1)) = c := by
  have : (0 : BitVec 32) - BitVec.ofNat 32 1 = BitVec.allOnes 32 := by decide
  rw [this, BitVec.and_allOnes, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

theorem sel1' (a c : BitVec 32) : c ^^^ ((a ^^^ c) &&& (0 - BitVec.ofNat 32 1)) = a := by
  have : (0 : BitVec 32) - BitVec.ofNat 32 1 = BitVec.allOnes 32 := by decide
  rw [this, BitVec.and_allOnes, BitVec.xor_comm a, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

section
variable {e : Nat} {b : BitVec 32}

/-- While swapping `x` and `y` from `s0`, after `n` limbs. -/
structure SwapInv (b : BitVec 32) (x y sw : Nat) (s0 : State) (n : Nat) (s : State) : Prop where
  rest : Rest [.r2, .r3, .r4] s0 s
  frame : Frame [⟨State.addr b + BitVec.ofNat 64 x, 4 * n⟩, ⟨State.addr b + BitVec.ofNat 64 y, 4 * n⟩]
    s0.mem s.mem
  lx : ∀ j < n, VG.Proof.X25519.Arm.limb s.mem (State.addr b) x j =
    sel sw (VG.Proof.X25519.Arm.limb s0.mem (State.addr b) x j) (VG.Proof.X25519.Arm.limb s0.mem (State.addr b) y j)
  ly : ∀ j < n, VG.Proof.X25519.Arm.limb s.mem (State.addr b) y j =
    sel sw (VG.Proof.X25519.Arm.limb s0.mem (State.addr b) y j) (VG.Proof.X25519.Arm.limb s0.mem (State.addr b) x j)

theorem cswap_ok {x y : Nat} (hx : x + 64 ≤ 4096) (hy : y + 64 ≤ 4096) (hxy : x + 64 ≤ y ∨ y + 64 ≤ x)
    {s0 : State} (hc : VG.Proof.X25519.Arm.CtxN e b s0) {sw : Nat} (hsw : sw ≤ 1) (h9 : s0.gpr .r9 = 0 - BitVec.ofNat 32 sw) :
    WP isa (.block (cswap x y)) s0 (VG.Proof.X25519.Arm.SwapInv b x y sw s0 16) := by
  refine wp_range_flatMap (M := isa) (VG.Proof.X25519.Arm.SwapInv b x y sw s0) (fun k s hk h => ?_) 16 (Nat.le_refl _) s0
    ⟨Rest.refl _ _, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _),
      fun _ h => absurd h (Nat.not_lt_zero _)⟩
  have hcs : VG.Proof.X25519.Arm.CtxN e b s := hc.of_rest h.rest (by decide)
  have wx : wd s.mem (State.addr b) (x + 4 * k) = VG.Proof.X25519.Arm.limb s0.mem (State.addr b) x k :=
    wd_frame h.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
      · exact Offset.disjoint _ (by omega) (by omega) (by omega)
  have wy : wd s.mem (State.addr b) (y + 4 * k) = VG.Proof.X25519.Arm.limb s0.mem (State.addr b) y k :=
    wd_frame h.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint _ (by omega) (by omega) (by omega)
      · exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
  unfold cswapStep
  refine VG.Proof.X25519.Arm.ldr0_ok hcs (d := x + 4 * k) (by omega) fun t1 v1 => ?_
  refine VG.Proof.X25519.Arm.ldr0_ok (hcs.of_rest (v1.rest (ws := [.r2]) (by decide)) (by decide)) (d := y + 4 * k) (by omega)
    fun t2 v2 => ?_
  refine wp_dp (op2_reg _ _) fun t3 v3 => wp_dp (op2_reg _ _) fun t4 v4 => ?_
  refine wp_dp (op2_reg _ _) fun t5 v5 => wp_dp (op2_reg _ _) fun t6 v6 => ?_
  have hr6 : Rest [.r2, .r3, .r4] s t6 :=
    (v1.rest (by decide)).trans ((v2.rest (by decide)).trans ((v3.rest (by decide)).trans
      ((v4.rest (by decide)).trans ((v5.rest (by decide)).trans (v6.rest (by decide))))))
  have hc6 : VG.Proof.X25519.Arm.CtxN e b t6 := hcs.of_rest hr6 (by decide)
  refine VG.Proof.X25519.Arm.str0_ok hc6 (d := x + 4 * k) (by omega) fun t7 v7 => ?_
  refine VG.Proof.X25519.Arm.str0_ok (hc6.of_rest (v7.rest []) (by decide)) (d := y + 4 * k) (by omega) fun t8 v8 => ?_
  refine WP.block_nil ?_
  -- The values.
  have eX : t2.gpr .r2 = s.mem.readW (State.addr b + BitVec.ofNat 64 (x + 4 * k)) 32 := by
    rw [v2.other _ (by decide), v1.gpr]
  have eY : t2.gpr .r3 = s.mem.readW (State.addr b + BitVec.ofNat 64 (y + 4 * k)) 32 := by
    rw [v2.gpr, v1.mem]
  have em : t3.gpr .r9 = 0 - BitVec.ofNat 32 sw := by
    rw [v3.other _ (by decide), v2.other _ (by decide), v1.other _ (by decide), h.rest.gpr _ (by decide), h9]
  have e6x : t6.gpr .r2 = t2.gpr .r2 ^^^ ((t2.gpr .r2 ^^^ t2.gpr .r3) &&& (0 - BitVec.ofNat 32 sw)) := by
    rw [v6.other _ (by decide), v5.gpr, v4.other _ (by decide), v3.other _ (by decide), v4.gpr]
    show _ ^^^ (t3.gpr .r4 &&& t3.gpr .r9) = _
    rw [v3.gpr, em]; rfl
  have e6y : t6.gpr .r3 = t2.gpr .r3 ^^^ ((t2.gpr .r2 ^^^ t2.gpr .r3) &&& (0 - BitVec.ofNat 32 sw)) := by
    rw [v6.gpr, v5.other _ (by decide), v4.other _ (by decide), v3.other _ (by decide), v5.other _ (by decide),
      v4.gpr]
    show _ ^^^ (t3.gpr .r4 &&& t3.gpr .r9) = _
    rw [v3.gpr, em]; rfl
  have hm8 : t8.mem = (s.mem.writeW (State.addr b + BitVec.ofNat 64 (x + 4 * k)) (t6.gpr .r2)).writeW
      (State.addr b + BitVec.ofNat 64 (y + 4 * k)) (t6.gpr .r3) := by
    rw [v8.mem, v7.gpr, v7.mem, v6.mem, v5.mem, v4.mem, v3.mem, v2.mem, v1.mem]
  have vx : (t6.gpr .r2).toNat = sel sw (VG.Proof.X25519.Arm.limb s0.mem (State.addr b) x k) (VG.Proof.X25519.Arm.limb s0.mem (State.addr b) y k) := by
    rw [e6x, eX, eY, ← wx, ← wy]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsw with rfl | rfl
    · rw [VG.Proof.X25519.Arm.sel0]; rfl
    · rw [VG.Proof.X25519.Arm.sel1]; rfl
  have vy : (t6.gpr .r3).toNat = sel sw (VG.Proof.X25519.Arm.limb s0.mem (State.addr b) y k) (VG.Proof.X25519.Arm.limb s0.mem (State.addr b) x k) := by
    rw [e6y, eX, eY, ← wx, ← wy]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsw with rfl | rfl
    · rw [VG.Proof.X25519.Arm.sel0']; rfl
    · rw [VG.Proof.X25519.Arm.sel1']; rfl
  refine ⟨h.rest.trans (hr6.trans ((v7.rest _).trans (v8.rest _))), ?_, fun j hj => ?_, fun j hj => ?_⟩
  · rw [hm8]
    refine ((h.frame.sub fun r hr => ?_).writeW (List.mem_cons_self ..) _
      (Offset.contains _ (Nat.le_add_right _ _) (by omega) (by omega))).writeW
      (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _
      (Offset.contains _ (Nat.le_add_right _ _) (by omega) (by omega))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by omega)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Region.sub_prefix (by omega)⟩
  · rw [VG.Proof.X25519.Arm.limb, hm8, wd_write_other _ _ _ (by omega) (by omega) (by omega)]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [wd_write_other _ _ _ (by omega) (by omega) (by omega)]; exact h.lx j hj
    · rw [wd_write_self, vx]
  · rw [VG.Proof.X25519.Arm.limb, hm8]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [wd_write_other _ _ _ (by omega) (by omega) (by omega),
        wd_write_other _ _ _ (by omega) (by omega) (by omega)]; exact h.ly j hj
    · rw [wd_write_self, vy]

end

end VG.Proof.X25519.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.Arm.Slots`. -/
section

/-!
# X25519 on 32-bit ARM: the field elements the working space holds

`SlotsOk m B qs v`: each slot `q` of `qs` holds limbs below `2¹⁶` of the
element `v q`. The field operations as updates of `v` (`mulS`, `addS`, `subS`,
`cswapS`), for slots whose separation from the output is decided on their
offsets (`Sep1`), and writing only the field area `[64, acc + 128)` of the
working space (`FA`), for the product at any `acc` (X25519's `ACC` or
Ed25519's).
-/

namespace VG.Proof.X25519.Arm

open VG VG.Arm VG.Impl.X25519.Arm
open VG.Spec.X25519 (P Fe)
open VG.Proof.X25519 (toFe toFe_mul toFe_add toFe_sub)

/-- Each slot `q` of `qs` holds limbs below `2¹⁶` of `v q`. -/
def SlotsOk (m : Mem) (B : Addr) (qs : List Nat) (v : Nat → Fe) : Prop :=
  ∀ q ∈ qs, VG.Proof.X25519.Arm.Lim m B q ∧ VG.Proof.X25519.Arm.FS m B q = v q

theorem SlotsOk.mono {m : Mem} {B : Addr} {qs qs' : List Nat} {v : Nat → Fe} (h : VG.Proof.X25519.Arm.SlotsOk m B qs v)
    (hs : ∀ q ∈ qs', q ∈ qs) : VG.Proof.X25519.Arm.SlotsOk m B qs' v := fun q hq => h q (hs q hq)

theorem SlotsOk.congr {m : Mem} {B : Addr} {qs : List Nat} {v w : Nat → Fe} (h : VG.Proof.X25519.Arm.SlotsOk m B qs v)
    (hs : ∀ q ∈ qs, v q = w q) : VG.Proof.X25519.Arm.SlotsOk m B qs w := fun q hq => ⟨(h q hq).1, (h q hq).2.trans (hs q hq)⟩

/-- `v` with the element `x` at `o`. -/
def upd (v : Nat → Fe) (o : Nat) (x : Fe) (q : Nat) : Fe := if q = o then x else v q

theorem upd_self (v : Nat → Fe) (o : Nat) (x : Fe) : VG.Proof.X25519.Arm.upd v o x o = x := by simp [VG.Proof.X25519.Arm.upd]

theorem upd_of_ne (v : Nat → Fe) {o q : Nat} (x : Fe) (h : q ≠ o) : VG.Proof.X25519.Arm.upd v o x q = v q := by simp [VG.Proof.X25519.Arm.upd, h]

/-- Every slot of `qs` is `o` or separate from it, and in `[64, acc)`. -/
def Sep1 (acc o : Nat) (qs : List Nat) : Bool :=
  qs.all fun q => (q == o || q + 64 ≤ o || o + 64 ≤ q) && 64 ≤ q && q + 64 ≤ acc

theorem sep1_get {acc o : Nat} {qs : List Nat} (h : VG.Proof.X25519.Arm.Sep1 acc o qs = true) {q : Nat} (hq : q ∈ qs) :
    (q = o ∨ q + 64 ≤ o ∨ o + 64 ≤ q) ∧ 64 ≤ q ∧ q + 64 ≤ acc := by
  have := List.all_eq_true.mp h q hq
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at this
  exact ⟨this.1.1.elim (fun h => h.elim .inl (fun h => .inr (.inl h))) (fun h => .inr (.inr h)),
    this.1.2, this.2⟩

/-- The field area `[64, acc + 128)` of the working space: the elements and
the product at `acc`. -/
abbrev FA (acc : Nat) (b : BitVec 32) : Region := ⟨State.addr b + BitVec.ofNat 64 64, acc + 64⟩

section
variable {e acc : Nat} {b : BitVec 32}

/-- The slots of `qs` other than `o` after a write of `o` (and `acc`). -/
theorem slots_after (hA : acc + 128 ≤ 4096) {o : Nat} {qs : List Nat} (hq : VG.Proof.X25519.Arm.Sep1 acc o qs = true)
    (ho : o + 64 ≤ acc) {m m' : Mem}
    (hf : Frame [⟨State.addr b + BitVec.ofNat 64 o, 64⟩, ⟨State.addr b + BitVec.ofNat 64 acc, 128⟩] m m')
    {v : Nat → Fe} (hS : VG.Proof.X25519.Arm.SlotsOk m (State.addr b) qs v) {q : Nat} (hq' : q ∈ qs) (hqo : q ≠ o) :
    VG.Proof.X25519.Arm.Lim m' (State.addr b) q ∧ VG.Proof.X25519.Arm.FS m' (State.addr b) q = v q := by
  obtain ⟨h1, h2, h3⟩ := VG.Proof.X25519.Arm.sep1_get hq hq'
  have e : ∀ k < 16, VG.Proof.X25519.Arm.limb m' (State.addr b) q k = VG.Proof.X25519.Arm.limb m (State.addr b) q k :=
    VG.Proof.X25519.Arm.limb_frame hf fun r hr k hk => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint _ (by omega) (by omega) (by omega)
      · exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
  refine ⟨fun k hk => by rw [e k hk]; exact (hS q hq').1 k hk, ?_⟩
  rw [VG.Proof.X25519.Arm.FS, VG.Proof.X25519.Arm.V, val16_congr e]; exact (hS q hq').2

theorem frame_FA (hA : acc + 128 ≤ 4096) {o : Nat} (ho : 64 ≤ o ∧ o + 64 ≤ acc) {m m' : Mem}
    (hf : Frame [⟨State.addr b + BitVec.ofNat 64 o, 64⟩, ⟨State.addr b + BitVec.ofNat 64 acc, 128⟩] m m') :
    Frame [VG.Proof.X25519.Arm.FA acc b] m m' := by
  refine hf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact Offset.sub _ (by omega) (by omega)

theorem mulS (hA : acc + 128 ≤ 4096) {o x y : Nat} {qs : List Nat} {v : Nat → Fe}
    (hq : VG.Proof.X25519.Arm.Sep1 acc o qs = true)
    (ho : 64 ≤ o ∧ o + 64 ≤ acc) (hx : x ∈ qs) (hy : y ∈ qs) {s : State} (hc : VG.Proof.X25519.Arm.CtxN e b s)
    (hS : VG.Proof.X25519.Arm.SlotsOk s.mem (State.addr b) qs v) :
    WP isa (mulAt acc o x y) s fun s' => Rest VG.Proof.X25519.Arm.clob s s' ∧ Frame [VG.Proof.X25519.Arm.FA acc b] s.mem s'.mem ∧
      VG.Proof.X25519.Arm.SlotsOk s'.mem (State.addr b) (o :: qs) (VG.Proof.X25519.Arm.upd v o (v x * v y)) := by
  refine WP.mono (VG.Proof.X25519.Arm.mul_ok hA ho.2 (VG.Proof.X25519.Arm.sep1_get hq hx).2.2 (VG.Proof.X25519.Arm.sep1_get hq hy).2.2 hc (hS x hx).1 (hS y hy).1)
    fun s' ⟨hr, hf, hl, hv⟩ => ⟨hr, VG.Proof.X25519.Arm.frame_FA hA ho hf, fun q hq' => ?_⟩
  by_cases hqo : q = o
  · subst hqo
    refine ⟨hl, ?_⟩
    rw [VG.Proof.X25519.Arm.upd_self, ← (hS x hx).2, ← (hS y hy).2]
    exact toFe_mul hv
  · rw [VG.Proof.X25519.Arm.upd_of_ne _ _ hqo]
    exact VG.Proof.X25519.Arm.slots_after hA hq ho.2 hf hS ((List.mem_cons.mp hq').resolve_left hqo) hqo

theorem frame_o {o : Nat} {m m' : Mem} (hf : Frame [⟨State.addr b + BitVec.ofNat 64 o, 64⟩] m m') :
    Frame [⟨State.addr b + BitVec.ofNat 64 o, 64⟩, ⟨State.addr b + BitVec.ofNat 64 acc, 128⟩] m m' :=
  hf.mono fun r hr => by simp [List.mem_singleton.mp hr]

theorem addS (hA : acc + 128 ≤ 4096) {o x y : Nat} {qs : List Nat} {v : Nat → Fe}
    (hq : VG.Proof.X25519.Arm.Sep1 acc o qs = true)
    (ho : 64 ≤ o ∧ o + 64 ≤ acc) (hx : x ∈ qs) (hy : y ∈ qs) {s : State} (hc : VG.Proof.X25519.Arm.CtxN e b s)
    (hS : VG.Proof.X25519.Arm.SlotsOk s.mem (State.addr b) qs v) :
    WP isa (.block (add o x y)) s fun s' => Rest VG.Proof.X25519.Arm.clob s s' ∧ Frame [VG.Proof.X25519.Arm.FA acc b] s.mem s'.mem ∧
      VG.Proof.X25519.Arm.SlotsOk s'.mem (State.addr b) (o :: qs) (VG.Proof.X25519.Arm.upd v o (v x + v y)) := by
  have hx' := VG.Proof.X25519.Arm.sep1_get hq hx
  have hy' := VG.Proof.X25519.Arm.sep1_get hq hy
  refine WP.mono (VG.Proof.X25519.Arm.add_ok (by omega) (by omega) (by omega)
    (hx'.1.elim (fun h => .inl h.symm) fun h => .inr h.symm) (hy'.1.elim (fun h => .inl h.symm) fun h => .inr h.symm)
    hc (hS x hx).1 (hS y hy).1) fun s' ⟨hr, hf, hl, hv⟩ => ⟨hr, VG.Proof.X25519.Arm.frame_FA hA ho (VG.Proof.X25519.Arm.frame_o hf), fun q hq' => ?_⟩
  by_cases hqo : q = o
  · subst hqo
    refine ⟨hl, ?_⟩
    rw [VG.Proof.X25519.Arm.upd_self, ← (hS x hx).2, ← (hS y hy).2]
    exact toFe_add hv
  · rw [VG.Proof.X25519.Arm.upd_of_ne _ _ hqo]
    exact VG.Proof.X25519.Arm.slots_after hA hq ho.2 (VG.Proof.X25519.Arm.frame_o hf) hS ((List.mem_cons.mp hq').resolve_left hqo) hqo

theorem subS (hA : acc + 128 ≤ 4096) {o x y : Nat} {qs : List Nat} {v : Nat → Fe}
    (hq : VG.Proof.X25519.Arm.Sep1 acc o qs = true)
    (ho : 64 ≤ o ∧ o + 64 ≤ acc) (hx : x ∈ qs) (hy : y ∈ qs) {s : State} (hc : VG.Proof.X25519.Arm.CtxN e b s)
    (hS : VG.Proof.X25519.Arm.SlotsOk s.mem (State.addr b) qs v) :
    WP isa (.block (sub o x y)) s fun s' => Rest VG.Proof.X25519.Arm.clob s s' ∧ Frame [VG.Proof.X25519.Arm.FA acc b] s.mem s'.mem ∧
      VG.Proof.X25519.Arm.SlotsOk s'.mem (State.addr b) (o :: qs) (VG.Proof.X25519.Arm.upd v o (v x - v y)) := by
  have hx' := VG.Proof.X25519.Arm.sep1_get hq hx
  have hy' := VG.Proof.X25519.Arm.sep1_get hq hy
  refine WP.mono (VG.Proof.X25519.Arm.sub_ok (by omega) (by omega) (by omega)
    (hx'.1.elim (fun h => .inl h.symm) fun h => .inr h.symm) (hy'.1.elim (fun h => .inl h.symm) fun h => .inr h.symm)
    hc (hS x hx).1 (hS y hy).1) fun s' ⟨hr, hf, hl, hv⟩ => ⟨hr, VG.Proof.X25519.Arm.frame_FA hA ho (VG.Proof.X25519.Arm.frame_o hf), fun q hq' => ?_⟩
  by_cases hqo : q = o
  · subst hqo
    refine ⟨hl, ?_⟩
    rw [VG.Proof.X25519.Arm.upd_self, ← (hS x hx).2, ← (hS y hy).2]
    exact toFe_sub hv
  · rw [VG.Proof.X25519.Arm.upd_of_ne _ _ hqo]
    exact VG.Proof.X25519.Arm.slots_after hA hq ho.2 (VG.Proof.X25519.Arm.frame_o hf) hS ((List.mem_cons.mp hq').resolve_left hqo) hqo

/-- The elements after swapping `x` and `y` if `sw = 1`. -/
def swapV (x y sw : Nat) (v : Nat → Fe) (q : Nat) : Fe :=
  if q = x then sel sw (v x) (v y) else if q = y then sel sw (v y) (v x) else v q

theorem cswapS (hA : acc + 128 ≤ 4096) {x y : Nat} {qs : List Nat} {v : Nat → Fe}
    (hq : VG.Proof.X25519.Arm.Sep1 acc x qs = true) (hq' : VG.Proof.X25519.Arm.Sep1 acc y qs = true)
    (hx : x ∈ qs) (hy : y ∈ qs) (hxy : x + 64 ≤ y ∨ y + 64 ≤ x) {s : State} (hc : VG.Proof.X25519.Arm.CtxN e b s) {sw : Nat}
    (hsw : sw ≤ 1) (h9 : s.gpr .r9 = 0 - BitVec.ofNat 32 sw) (hS : VG.Proof.X25519.Arm.SlotsOk s.mem (State.addr b) qs v) :
    WP isa (.block (cswap x y)) s fun s' => Rest [.r2, .r3, .r4] s s' ∧ Frame [VG.Proof.X25519.Arm.FA acc b] s.mem s'.mem ∧
      VG.Proof.X25519.Arm.SlotsOk s'.mem (State.addr b) qs (VG.Proof.X25519.Arm.swapV x y sw v) := by
  have hx' := VG.Proof.X25519.Arm.sep1_get hq hx
  have hy' := VG.Proof.X25519.Arm.sep1_get hq hy
  refine WP.mono (VG.Proof.X25519.Arm.cswap_ok (b := b) (by omega) (by omega) hxy hc hsw h9) fun s' h => ⟨h.rest, ?_, ?_⟩
  · refine h.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Offset.sub _ (by omega) (by omega)
  · intro q hq''
    have hlx : ∀ k < 16, VG.Proof.X25519.Arm.limb s'.mem (State.addr b) x k =
        sel sw (VG.Proof.X25519.Arm.limb s.mem (State.addr b) x k) (VG.Proof.X25519.Arm.limb s.mem (State.addr b) y k) := h.lx
    have hly : ∀ k < 16, VG.Proof.X25519.Arm.limb s'.mem (State.addr b) y k =
        sel sw (VG.Proof.X25519.Arm.limb s.mem (State.addr b) y k) (VG.Proof.X25519.Arm.limb s.mem (State.addr b) x k) := h.ly
    by_cases hqx : q = x
    · subst hqx
      simp only [VG.Proof.X25519.Arm.swapV, ite_true]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsw with rfl | rfl
      · have e : ∀ k < 16, VG.Proof.X25519.Arm.limb s'.mem (State.addr b) q k = VG.Proof.X25519.Arm.limb s.mem (State.addr b) q k :=
          fun k hk => by rw [hlx k hk]; rfl
        refine ⟨fun k hk => by rw [e k hk]; exact (hS q hx).1 k hk, ?_⟩
        rw [VG.Proof.X25519.Arm.FS, VG.Proof.X25519.Arm.V, val16_congr e]; exact (hS q hx).2
      · have e : ∀ k < 16, VG.Proof.X25519.Arm.limb s'.mem (State.addr b) q k = VG.Proof.X25519.Arm.limb s.mem (State.addr b) y k :=
          fun k hk => by rw [hlx k hk]; rfl
        refine ⟨fun k hk => by rw [e k hk]; exact (hS y hy).1 k hk, ?_⟩
        rw [VG.Proof.X25519.Arm.FS, VG.Proof.X25519.Arm.V, val16_congr e]; exact (hS y hy).2
    by_cases hqy : q = y
    · subst hqy
      simp only [VG.Proof.X25519.Arm.swapV, hqx, ite_false, ite_true]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsw with rfl | rfl
      · have e : ∀ k < 16, VG.Proof.X25519.Arm.limb s'.mem (State.addr b) q k = VG.Proof.X25519.Arm.limb s.mem (State.addr b) q k :=
          fun k hk => by rw [hly k hk]; rfl
        refine ⟨fun k hk => by rw [e k hk]; exact (hS q hy).1 k hk, ?_⟩
        rw [VG.Proof.X25519.Arm.FS, VG.Proof.X25519.Arm.V, val16_congr e]; exact (hS q hy).2
      · have e : ∀ k < 16, VG.Proof.X25519.Arm.limb s'.mem (State.addr b) q k = VG.Proof.X25519.Arm.limb s.mem (State.addr b) x k :=
          fun k hk => by rw [hly k hk]; rfl
        refine ⟨fun k hk => by rw [e k hk]; exact (hS x hx).1 k hk, ?_⟩
        rw [VG.Proof.X25519.Arm.FS, VG.Proof.X25519.Arm.V, val16_congr e]; exact (hS x hx).2
    · simp only [VG.Proof.X25519.Arm.swapV, hqx, hqy, ite_false]
      obtain ⟨h1, h2, h3⟩ := VG.Proof.X25519.Arm.sep1_get hq hq''
      obtain ⟨h1', -, -⟩ := VG.Proof.X25519.Arm.sep1_get hq' hq''
      have e : ∀ k < 16, VG.Proof.X25519.Arm.limb s'.mem (State.addr b) q k = VG.Proof.X25519.Arm.limb s.mem (State.addr b) q k :=
        VG.Proof.X25519.Arm.limb_frame h.frame fun r hr k hk => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact Offset.disjoint _ (by omega) (by omega) (by omega)
          · exact Offset.disjoint _ (by omega) (by omega) (by omega)
      refine ⟨fun k hk => by rw [e k hk]; exact (hS q hq'').1 k hk, ?_⟩
      rw [VG.Proof.X25519.Arm.FS, VG.Proof.X25519.Arm.V, val16_congr e]; exact (hS q hq'').2

end

end VG.Proof.X25519.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.Arm.Ladder`. -/
section

/-!
# X25519 on 32-bit ARM: the ladder

One iteration of the ladder (`step_ok`) takes the elements `x1, x2, z2, x3,
z3, a24` from the state after the bits `254` down to `n` (`ladderAfter k x1
n`) to the state after `n - 1`, with the swap in `r10` and the counter in
`r11`; the loop (`ladder_ok`) runs it for the bits 254 down to 0.
-/

namespace VG.Proof.X25519.Arm

open VG VG.Arm VG.Impl.X25519.Arm
open VG.Spec.X25519 (P Fe Ladder ladderStep cswap a24)
open VG.Proof.X25519 (toFe ladderAfter ladderAfter_step ladderStep_eq bit bit_le ladderAfter_swap_le)

/-- `s'` is `s` but for the registers `r1`–`r11`, the flags and the field
area. -/
structure Stp (b : BitVec 32) (s s' : State) : Prop where
  rest : Rest [.r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11] s s'
  frame : Frame [VG.Proof.X25519.Arm.FA ACC b] s.mem s'.mem

theorem Stp.refl (b : BitVec 32) (s : State) : VG.Proof.X25519.Arm.Stp b s s := ⟨Rest.refl _ _, Frame.refl _ _⟩

theorem Stp.trans {b : BitVec 32} {s₁ s₂ s₃ : State} (h₁ : VG.Proof.X25519.Arm.Stp b s₁ s₂) (h₂ : VG.Proof.X25519.Arm.Stp b s₂ s₃) : VG.Proof.X25519.Arm.Stp b s₁ s₃ :=
  ⟨h₁.rest.trans h₂.rest, h₁.frame.trans h₂.frame⟩

theorem Stp.of_rest {b : BitVec 32} {s s' : State} {ws : List Reg} (hr : Rest ws s s')
    (hws : ∀ r ∈ ws, r ∈ [Reg.r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11])
    (hm : s'.mem = s.mem) : VG.Proof.X25519.Arm.Stp b s s' := ⟨hr.mono hws, by rw [hm]; exact Frame.refl _ _⟩

/-- Between field operations, from `s0`: `r10` and `r11` hold `a` and `c`,
and the slots `qs` the elements `v`. -/
structure Cur (b : BitVec 32) (s0 : State) (a c : BitVec 32) (qs : List Nat) (v : Nat → Fe) (s : State) :
    Prop where
  ctx : VG.Proof.X25519.Arm.Ctx b s
  stp : VG.Proof.X25519.Arm.Stp b s0 s
  r10 : s.gpr .r10 = a
  r11 : s.gpr .r11 = c
  slots : VG.Proof.X25519.Arm.SlotsOk s.mem (State.addr b) qs v

section
variable {b : BitVec 32} {s0 : State} {a c : BitVec 32} {qs : List Nat} {v : Nat → Fe}

theorem Cur.next {s s' : State} (h : VG.Proof.X25519.Arm.Cur b s0 a c qs v s) (hr : Rest VG.Proof.X25519.Arm.clob s s')
    (hf : Frame [VG.Proof.X25519.Arm.FA ACC b] s.mem s'.mem) {qs' : List Nat} {v' : Nat → Fe}
    (hS : VG.Proof.X25519.Arm.SlotsOk s'.mem (State.addr b) qs' v') : VG.Proof.X25519.Arm.Cur b s0 a c qs' v' s' :=
  ⟨h.ctx.of_rest hr (by decide), h.stp.trans ⟨hr.mono (by decide), hf⟩,
    by rw [hr.gpr _ (by decide), h.r10], by rw [hr.gpr _ (by decide), h.r11], hS⟩

theorem opMul {o x y : Nat} (hq : VG.Proof.X25519.Arm.Sep1 ACC o qs = true) (ho : 64 ≤ o ∧ o + 64 ≤ ACC) (hx : x ∈ qs)
    (hy : y ∈ qs) {s : State} (h : VG.Proof.X25519.Arm.Cur b s0 a c qs v s) :
    WP isa (mul o x y) s (VG.Proof.X25519.Arm.Cur b s0 a c (o :: qs) (VG.Proof.X25519.Arm.upd v o (v x * v y))) :=
  WP.mono (VG.Proof.X25519.Arm.mulS (by decide) hq ho hx hy h.ctx h.slots) fun _ ⟨hr, hf, hS⟩ => h.next hr hf hS

theorem opAdd {o x y : Nat} (hq : VG.Proof.X25519.Arm.Sep1 ACC o qs = true) (ho : 64 ≤ o ∧ o + 64 ≤ ACC) (hx : x ∈ qs)
    (hy : y ∈ qs) {s : State} (h : VG.Proof.X25519.Arm.Cur b s0 a c qs v s) :
    WP isa (.block (add o x y)) s (VG.Proof.X25519.Arm.Cur b s0 a c (o :: qs) (VG.Proof.X25519.Arm.upd v o (v x + v y))) :=
  WP.mono (VG.Proof.X25519.Arm.addS (by decide) hq ho hx hy h.ctx h.slots) fun _ ⟨hr, hf, hS⟩ => h.next hr hf hS

theorem opSub {o x y : Nat} (hq : VG.Proof.X25519.Arm.Sep1 ACC o qs = true) (ho : 64 ≤ o ∧ o + 64 ≤ ACC) (hx : x ∈ qs)
    (hy : y ∈ qs) {s : State} (h : VG.Proof.X25519.Arm.Cur b s0 a c qs v s) :
    WP isa (.block (sub o x y)) s (VG.Proof.X25519.Arm.Cur b s0 a c (o :: qs) (VG.Proof.X25519.Arm.upd v o (v x - v y))) :=
  WP.mono (VG.Proof.X25519.Arm.subS (by decide) hq ho hx hy h.ctx h.slots) fun _ ⟨hr, hf, hS⟩ => h.next hr hf hS

end

/-! ## Sequences of field operations -/

/-- A field operation: `o = x · y`, `x + y` or `x - y`. -/
inductive FOp
  | mul (o x y : Nat)
  | add (o x y : Nat)
  | sub (o x y : Nat)

def FOp.code : VG.Proof.X25519.Arm.FOp → Prog isa
  | .mul o x y => Impl.X25519.Arm.mul o x y
  | .add o x y => .block (Impl.X25519.Arm.add o x y)
  | .sub o x y => .block (Impl.X25519.Arm.sub o x y)

def FOp.out : VG.Proof.X25519.Arm.FOp → Nat
  | .mul o _ _ | .add o _ _ | .sub o _ _ => o

def FOp.x : VG.Proof.X25519.Arm.FOp → Nat
  | .mul _ x _ | .add _ x _ | .sub _ x _ => x

def FOp.y : VG.Proof.X25519.Arm.FOp → Nat
  | .mul _ _ y | .add _ _ y | .sub _ _ y => y

def FOp.val : VG.Proof.X25519.Arm.FOp → (Nat → Fe) → Fe
  | .mul _ x y, v => v x * v y
  | .add _ x y, v => v x + v y
  | .sub _ x y, v => v x - v y

/-- The operations `ops`, then `k`. -/
def opsCode : List VG.Proof.X25519.Arm.FOp → Prog isa → Prog isa
  | [], k => k
  | op :: ops, k => .seq op.code (VG.Proof.X25519.Arm.opsCode ops k)

/-- Each operation's slots are separate or equal, below `ACC`, and its inputs
known. -/
def opsOk : List VG.Proof.X25519.Arm.FOp → List Nat → Bool
  | [], _ => true
  | op :: ops, qs => VG.Proof.X25519.Arm.Sep1 ACC op.out qs && 64 ≤ op.out && op.out + 64 ≤ ACC && qs.contains op.x &&
      qs.contains op.y && VG.Proof.X25519.Arm.opsOk ops (op.out :: qs)

/-- The elements after the operations. -/
def runOps : List VG.Proof.X25519.Arm.FOp → (Nat → Fe) → Nat → Fe
  | [], v => v
  | op :: ops, v => VG.Proof.X25519.Arm.runOps ops (VG.Proof.X25519.Arm.upd v op.out (op.val v))

/-- The slots known after the operations. -/
def outsQ : List VG.Proof.X25519.Arm.FOp → List Nat → List Nat
  | [], qs => qs
  | op :: ops, qs => VG.Proof.X25519.Arm.outsQ ops (op.out :: qs)

theorem op_ok {b : BitVec 32} {s0 : State} {a c : BitVec 32} {qs : List Nat} {v : Nat → Fe} (op : VG.Proof.X25519.Arm.FOp)
    (hq : VG.Proof.X25519.Arm.Sep1 ACC op.out qs = true) (ho : 64 ≤ op.out ∧ op.out + 64 ≤ ACC) (hx : op.x ∈ qs) (hy : op.y ∈ qs)
    {s : State} (h : VG.Proof.X25519.Arm.Cur b s0 a c qs v s) :
    WP isa op.code s (VG.Proof.X25519.Arm.Cur b s0 a c (op.out :: qs) (VG.Proof.X25519.Arm.upd v op.out (op.val v))) := by
  cases op with
  | mul o x y => exact VG.Proof.X25519.Arm.opMul hq ho hx hy h
  | add o x y => exact VG.Proof.X25519.Arm.opAdd hq ho hx hy h
  | sub o x y => exact VG.Proof.X25519.Arm.opSub hq ho hx hy h

theorem ops_ok {b : BitVec 32} {s0 : State} {a c : BitVec 32} {k : Prog isa} {Q : State → Prop} :
    ∀ (ops : List VG.Proof.X25519.Arm.FOp) (qs : List Nat) (v : Nat → Fe) (s : State), VG.Proof.X25519.Arm.opsOk ops qs = true →
      VG.Proof.X25519.Arm.Cur b s0 a c qs v s → (∀ s', VG.Proof.X25519.Arm.Cur b s0 a c (VG.Proof.X25519.Arm.outsQ ops qs) (VG.Proof.X25519.Arm.runOps ops v) s' → WP isa k s' Q) →
      WP isa (VG.Proof.X25519.Arm.opsCode ops k) s Q
  | [], _, _, s, _, h, hk => hk s h
  | op :: ops, qs, v, s, hok, h, hk => by
    simp only [VG.Proof.X25519.Arm.opsOk, Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at hok
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hok
    exact WP.seq (WP.mono (VG.Proof.X25519.Arm.op_ok op h1 ⟨h2, h3⟩ h4 h5 h) fun s' h' => VG.Proof.X25519.Arm.ops_ok ops _ _ s' h6 h' hk)

/-! ## One iteration -/

/-- The field operations of an iteration, after the swaps. -/
def ladOps : List VG.Proof.X25519.Arm.FOp :=
  [.add A X2 Z2, .mul AA A A, .sub B X2 Z2, .mul BB B B, .sub E AA BB, .add C X3 Z3, .sub D X3 Z3,
    .mul DA D A, .mul CB C B, .add X3 DA CB, .mul X3 X3 X3, .sub Z3 DA CB, .mul Z3 Z3 Z3,
    .mul Z3 X1 Z3, .mul X2 AA BB, .mul Z2 A24 E, .add Z2 AA Z2, .mul Z2 E Z2]

/-- The slots the ladder's state lives in. -/
def LQ : List Nat := [X1, X2, Z2, X3, Z3, A24]

theorem ladOps_ok : VG.Proof.X25519.Arm.opsOk VG.Proof.X25519.Arm.ladOps VG.Proof.X25519.Arm.LQ = true := by decide

/-- The elements of the ladder's state `st`, and `x1` and `a24`. -/
def ladV (x1 : Fe) (st : Ladder) (q : Nat) : Fe :=
  if q = X1 then x1 else if q = X2 then st.x2 else if q = Z2 then st.z2 else if q = X3 then st.x3
  else if q = Z3 then st.z3 else a24

theorem cswap_fst (sw : Nat) (x y : Fe) : (Spec.X25519.cswap sw x y).1 = sel sw x y := by
  unfold Spec.X25519.cswap sel; split <;> rfl

theorem cswap_snd (sw : Nat) (x y : Fe) : (Spec.X25519.cswap sw x y).2 = sel sw y x := by
  unfold Spec.X25519.cswap sel; split <;> rfl

/-- The elements after an iteration. -/
theorem ladOps_vals (k : Nat) (x1 : Fe) (st : Ladder) (t : Nat) :
    ∀ q ∈ VG.Proof.X25519.Arm.LQ, VG.Proof.X25519.Arm.runOps VG.Proof.X25519.Arm.ladOps (VG.Proof.X25519.Arm.swapV Z2 Z3 (st.swap ^^^ VG.Proof.X25519.bit k t) (VG.Proof.X25519.Arm.swapV X2 X3 (st.swap ^^^ VG.Proof.X25519.bit k t)
      (VG.Proof.X25519.Arm.ladV x1 st))) q = VG.Proof.X25519.Arm.ladV x1 (ladderStep k x1 st t) q := by
  intro q hq
  rw [ladderStep_eq]
  simp only [VG.Proof.X25519.Arm.LQ, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [VG.Proof.X25519.Arm.ladOps, VG.Proof.X25519.Arm.runOps, FOp.out, FOp.val, VG.Proof.X25519.Arm.upd, VG.Proof.X25519.Arm.swapV, VG.Proof.X25519.Arm.ladV, VG.Proof.X25519.Arm.cswap_fst, VG.Proof.X25519.Arm.cswap_snd, X1, X2, Z2, X3,
      Z3, A, B, C, D, AA, BB, E, DA, CB, A24, Nat.reduceEqDiff, ite_true, ite_false]

theorem ofNat_xor {x y : Nat} (hx : x < 2 ^ 32) (hy : y < 2 ^ 32) :
    BitVec.ofNat 32 x ^^^ BitVec.ofNat 32 y = BitVec.ofNat 32 (x ^^^ y) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_xor, toNat_imm hx, toNat_imm hy, toNat_imm (Nat.xor_lt_two_pow hx hy)]

theorem xor_le_one {x y : Nat} (hx : x ≤ 1) (hy : y ≤ 1) : x ^^^ y ≤ 1 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hx with rfl | rfl <;>
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hy with rfl | rfl <;> decide

theorem ea2 {b : BitVec 32} (hfit : b.toNat + 4096 ≤ 2 ^ 32) {x d : Nat} (h : x + d < 4096) :
    State.addr (b + BitVec.ofNat 32 x + BitVec.ofNat 32 d) = State.addr b + BitVec.ofNat 64 (x + d) := by
  rw [Offset.add_add]; exact addr_add (by omega)

/-- The loop invariant of the ladder from `sL`, before the iteration for the
bit `n - 1`. -/
structure LadInv (b : BitVec 32) (k : Nat) (x1 : Fe) (sL : State) (n : Nat) (s : State) : Prop where
  cur : VG.Proof.X25519.Arm.Cur b sL (BitVec.ofNat 32 (ladderAfter k x1 n).swap) (BitVec.ofNat 32 n) VG.Proof.X25519.Arm.LQ
    (VG.Proof.X25519.Arm.ladV x1 (ladderAfter k x1 n)) s

/-- The bits of the scalar in `BITS`. -/
def Bits (b : BitVec 32) (k : Nat) (m : Mem) : Prop :=
  ∀ t < 255, m (State.addr b + BitVec.ofNat 64 (BITS + t)) = BitVec.ofNat 8 (VG.Proof.X25519.bit k t)

theorem head_ok {b : BitVec 32} {k : Nat} {x1 : Fe} {sL : State} (hbits : VG.Proof.X25519.Arm.Bits b k sL.mem)
    {n : Nat} (hn : 1 ≤ n) (hn' : n ≤ 255) {s : State} (h : VG.Proof.X25519.Arm.LadInv b k x1 sL n s) :
    WP isa (.block stepHead) s (VG.Proof.X25519.Arm.Cur b sL (BitVec.ofNat 32 (VG.Proof.X25519.bit k (n - 1))) (BitVec.ofNat 32 (n - 1)) VG.Proof.X25519.Arm.LQ
      (VG.Proof.X25519.Arm.swapV Z2 Z3 ((ladderAfter k x1 n).swap ^^^ VG.Proof.X25519.bit k (n - 1))
        (VG.Proof.X25519.Arm.swapV X2 X3 ((ladderAfter k x1 n).swap ^^^ VG.Proof.X25519.bit k (n - 1)) (VG.Proof.X25519.Arm.ladV x1 (ladderAfter k x1 n))))) := by
  obtain ⟨hcur⟩ := h
  have hc := hcur.ctx
  have hfit := hc.fit
  have hB : BITS = 1280 := rfl
  have hsw := ladderAfter_swap_le k x1 hn'
  have hbt := bit_le k (n - 1)
  have hx := VG.Proof.X25519.Arm.xor_le_one hsw hbt
  simp only [stepHead, mask, List.append_assoc, List.cons_append, List.nil_append]
  refine wp_dp (op2_imm (by decide)) fun s1 u1 => ?_
  have e11 : s1.gpr .r11 = BitVec.ofNat 32 (n - 1) := by
    rw [u1.gpr]; show s.gpr .r11 - 1 = _
    rw [hcur.r11]
    apply BitVec.eq_of_toNat_eq
    have t1 : (1 : BitVec 32).toNat = 1 := rfl
    rw [toNat_sub_le (by rw [toNat_imm (by omega), t1]; omega), toNat_imm (by omega), toNat_imm (by omega), t1]
  refine wp_dp (op2_reg _ _) fun s2 u2 => ?_
  refine wp_ldrb (a := State.addr b + BitVec.ofNat 64 (n - 1 + BITS)) (by decide)
    (by rw [u2.gpr]; show State.addr (s1.gpr .r0 + s1.gpr .r11 + _) = _
        rw [e11, u1.other _ (by decide), hc.r0, VG.Proof.X25519.Arm.ea2 hfit (by omega)])
    (by rw [u2.rd, u2.wr, u1.rd, u1.wr]; exact hc.inR (by omega)) fun s3 u3 => ?_
  have e1 : s3.gpr .r1 = BitVec.ofNat 32 (VG.Proof.X25519.bit k (n - 1)) := by
    rw [u3.gpr, u2.mem, u1.mem, hcur.stp.frame _ fun r hr => ?_, Nat.add_comm, hbits _ (by omega)]
    · apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, toNat_imm (by omega)]; omega
    · rw [List.mem_singleton.mp hr]
      exact fun h => by
        simp only [Region.Contains] at h
        rw [Offset.sub_toNat _ (by omega) (by omega)] at h
        have := VG.Proof.X25519.Arm.ACC_eq
        omega
  refine wp_dp (op2_reg _ _) fun s4 u4 => ?_
  have e10 : s4.gpr .r10 = BitVec.ofNat 32 ((ladderAfter k x1 n).swap ^^^ VG.Proof.X25519.bit k (n - 1)) := by
    rw [u4.gpr]; show s3.gpr .r10 ^^^ s3.gpr .r1 = _
    rw [e1, u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide), hcur.r10,
      VG.Proof.X25519.Arm.ofNat_xor (by omega) (by omega)]
  refine wp_mov (op2_imm (by decide)) fun s5 u5 => wp_dp (op2_reg _ _) fun s6 u6 => ?_
  have e9 : s6.gpr .r9 = 0 - BitVec.ofNat 32 ((ladderAfter k x1 n).swap ^^^ VG.Proof.X25519.bit k (n - 1)) := by
    rw [u6.gpr]; show s5.gpr .r9 - s5.gpr .r10 = _
    rw [u5.gpr, u5.other _ (by decide), e10]
  have hr6 : Rest [.r1, .r9, .r10, .r11] s s6 :=
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
      ((u4.rest (by decide)).trans ((u5.rest (by decide)).trans (u6.rest (by decide))))))
  have hm6 : s6.mem = s.mem := by rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  have hc6 : VG.Proof.X25519.Arm.Ctx b s6 := hc.of_rest hr6 (by decide)
  have hS6 : VG.Proof.X25519.Arm.SlotsOk s6.mem (State.addr b) VG.Proof.X25519.Arm.LQ (VG.Proof.X25519.Arm.ladV x1 (ladderAfter k x1 n)) := by
    rw [hm6]; exact hcur.slots
  refine WP.append (VG.Proof.X25519.Arm.cswapS (acc := ACC) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) hc6 hx e9 hS6)
    fun s7 ⟨hr7, hf7, hS7⟩ => ?_
  have hc7 : VG.Proof.X25519.Arm.Ctx b s7 := hc6.of_rest hr7 (by decide)
  refine WP.append (VG.Proof.X25519.Arm.cswapS (acc := ACC) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) hc7 hx
    (by rw [hr7.gpr _ (by decide), e9]) hS7) fun s8 ⟨hr8, hf8, hS8⟩ => ?_
  refine wp_mov (op2_reg _ _) fun s9 u9 => WP.block_nil ?_
  have hr9 : Rest [.r1, .r2, .r3, .r4, .r9, .r10, .r11] s s9 :=
    (hr6.mono (by decide)).trans ((hr7.mono (by decide)).trans ((hr8.mono (by decide)).trans
      (u9.rest (by decide))))
  exact ⟨hc.of_rest hr9 (by decide),
    hcur.stp.trans ⟨hr9.mono (by decide), by rw [u9.mem, ← hm6]; exact hf7.trans hf8⟩,
    by rw [u9.gpr, hr8.gpr _ (by decide), hr7.gpr _ (by decide), u6.other _ (by decide),
      u5.other _ (by decide), u4.other _ (by decide), e1],
    by rw [u9.other _ (by decide), hr8.gpr _ (by decide), hr7.gpr _ (by decide), u6.other _ (by decide),
      u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), e11],
    by rw [u9.mem]; exact hS8⟩

theorem sub0 (x : BitVec 32) : x - 0 = x := by simp

theorem step_eq : VG.Impl.X25519.Arm.step = .seq (.block stepHead) (VG.Proof.X25519.Arm.opsCode VG.Proof.X25519.Arm.ladOps (.block [.cmp .r11 (.imm 0)])) := rfl

theorem step_ok {b : BitVec 32} {k : Nat} {x1 : Fe} {sL : State} (hbits : VG.Proof.X25519.Arm.Bits b k sL.mem)
    {n : Nat} (hn : 1 ≤ n) (hn' : n ≤ 255) {s : State} (h : VG.Proof.X25519.Arm.LadInv b k x1 sL n s) :
    WP isa VG.Impl.X25519.Arm.step s fun s' => VG.Proof.X25519.Arm.LadInv b k x1 sL (n - 1) s' ∧ s'.z = decide (n - 1 = 0) := by
  rw [VG.Proof.X25519.Arm.step_eq]
  refine WP.seq (WP.mono (VG.Proof.X25519.Arm.head_ok hbits hn hn' h) fun s1 h1 =>
    VG.Proof.X25519.Arm.ops_ok VG.Proof.X25519.Arm.ladOps VG.Proof.X25519.Arm.LQ _ s1 VG.Proof.X25519.Arm.ladOps_ok h1 fun s2 h2 => ?_)
  refine wp_cmp (op2_imm (by decide)) fun s3 u3 hz => WP.block_nil ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact h2.ctx.of_rest (u3.rest []) (by decide)
  · exact h2.stp.trans (Stp.of_rest (u3.rest []) (by decide) u3.mem)
  · rw [u3.gpr, h2.r10, ladderAfter_step k x1 (show n - 1 < 255 by omega), Nat.sub_add_cancel hn,
      ladderStep_eq]
  · rw [u3.gpr, h2.r11]
  · rw [u3.mem]
    refine (h2.slots.mono (by decide)).congr fun q hq => ?_
    rw [ladderAfter_step k x1 (show n - 1 < 255 by omega), Nat.sub_add_cancel hn]
    exact VG.Proof.X25519.Arm.ladOps_vals k x1 _ (n - 1) q hq
  · rw [hz, h2.r11, VG.Proof.X25519.Arm.sub0, ofNat_beq_zero (by omega)]

/-- The ladder, from the state with the bits of the scalar in `BITS` and the
initial elements in `LQ`. -/
theorem ladder_ok {b : BitVec 32} {k : Nat} {x1 : Fe} {s : State} (hc : VG.Proof.X25519.Arm.Ctx b s) (hbits : VG.Proof.X25519.Arm.Bits b k s.mem)
    (hS : VG.Proof.X25519.Arm.SlotsOk s.mem (State.addr b) VG.Proof.X25519.Arm.LQ (VG.Proof.X25519.Arm.ladV x1 (VG.Proof.X25519.init x1))) :
    WP isa ladder s fun s' => VG.Proof.X25519.Arm.Stp b s s' ∧ VG.Proof.X25519.Arm.Ctx b s' ∧
      s'.gpr .r10 = BitVec.ofNat 32 (ladderAfter k x1 0).swap ∧
      VG.Proof.X25519.Arm.SlotsOk s'.mem (State.addr b) VG.Proof.X25519.Arm.LQ (VG.Proof.X25519.Arm.ladV x1 (ladderAfter k x1 0)) := by
  unfold ladder
  refine WP.seq (wp_mov (op2_imm (by decide)) fun s1 u1 => wp_mov (op2_imm (by decide)) fun s2 u2 =>
    WP.block_nil ?_)
  have hr2 : Rest [.r10, .r11] s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  have hm2 : s2.mem = s.mem := by rw [u2.mem, u1.mem]
  have hbits2 : VG.Proof.X25519.Arm.Bits b k s2.mem := by rw [hm2]; exact hbits
  have h255 : VG.Proof.X25519.Arm.LadInv b k x1 s2 255 s2 :=
    ⟨⟨hc.of_rest hr2 (by decide), Stp.refl _ _, by rw [u2.gpr]; rfl,
      by rw [u2.other _ (by decide), u1.gpr]; rfl, by rw [hm2]; exact hS⟩⟩
  have hst : VG.Proof.X25519.Arm.Stp b s s2 := Stp.of_rest hr2 (by decide) hm2
  refine WP.mono (Q := VG.Proof.X25519.Arm.LadInv b k x1 s2 0) (WP.loop (M := isa)
    (fun m s' => 1 ≤ m ∧ m ≤ 255 ∧ VG.Proof.X25519.Arm.LadInv b k x1 s2 m s') ?_ 255 s2 ⟨by decide, Nat.le_refl _, h255⟩)
    fun s' ⟨h'⟩ => ⟨hst.trans h'.stp, h'.ctx, h'.r10, h'.slots⟩
  rintro m s' ⟨h1, h2, hl⟩
  refine WP.mono (VG.Proof.X25519.Arm.step_ok hbits2 h1 h2 hl) fun s'' ⟨hl', hz⟩ => ?_
  by_cases hm : m - 1 = 0
  · exact .inl ⟨by rw [eval_ne, hz]; simp [hm], by rw [hm] at hl'; exact hl'⟩
  · exact .inr ⟨by rw [eval_ne, hz]; simp [hm], m - 1, by omega, by omega, by omega, hl'⟩

end VG.Proof.X25519.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.Arm.Invert`. -/
section

/-!
# X25519 on 32-bit ARM: the inversion

`invert` computes `z^(p-2)` into `R` for the element `z` at `Z2` by
square-and-multiply over the bits of `p - 2` from 254 down to 0 (`invert_ok`):
after the bits down to `n`, `R` holds `z^((p - 2) >> n)`.
-/

namespace VG.Proof.X25519.Arm

open VG VG.Arm VG.Impl.X25519.Arm
open VG.Spec.X25519 (P Fe)

/-! ## The bits of `p - 2` -/

def pbitsB : Nat → Bool
  | 0 => true
  | t + 1 => ((P - 2) >>> t % 2 == if t = 4 ∨ t = 2 then 0 else 1) && VG.Proof.X25519.Arm.pbitsB t

theorem pbitsB_ok : VG.Proof.X25519.Arm.pbitsB 255 = true := by decide +kernel

/-- Every bit of `p - 2 = 2²⁵⁵ - 21` but bits 4 and 2 (and those from 255 up) is 1. -/
theorem pbits : ∀ t < 255, (P - 2) >>> t % 2 = if t = 4 ∨ t = 2 then 0 else 1 := by
  have : ∀ n, VG.Proof.X25519.Arm.pbitsB n = true → ∀ t < n, (P - 2) >>> t % 2 = if t = 4 ∨ t = 2 then 0 else 1 := by
    intro n; induction n with
    | zero => intro _ t ht; omega
    | succ n ih =>
      intro h t ht
      simp only [VG.Proof.X25519.Arm.pbitsB, Bool.and_eq_true, beq_iff_eq] at h
      rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht | rfl
      · exact ih h.2 t ht
      · exact h.1
  exact this 255 VG.Proof.X25519.Arm.pbitsB_ok

theorem p255 : (P - 2) >>> 255 = 0 := by decide +kernel

theorem iteT {c : Prop} [Decidable c] {α : Type} {a b : α} (h : c) : (if c then a else b) = a := by
  simp [h]

theorem iteF {c : Prop} [Decidable c] {α : Type} {a b : α} (h : ¬c) : (if c then a else b) = b := by
  simp [h]

theorem shr_step (x t : Nat) : x >>> t = 2 * (x >>> (t + 1)) + x >>> t % 2 := by
  rw [Nat.shiftRight_succ]; omega

/-! ## Stores of a register -/

section
variable {b : BitVec 32}

/-- Stores of register `r` into the `n` words from `o`. -/
theorem stores_ok {r : Reg} {o n : Nat} (ho : o + 4 * n ≤ 4096) {s : State} (hc : VG.Proof.X25519.Arm.Ctx b s) :
    WP isa (.block (storeN r o n)) s fun s' =>
      (∀ j < n, wd s'.mem (State.addr b) (o + 4 * j) = (s.gpr r).toNat) ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 o, 4 * n⟩] s.mem s'.mem ∧ s'.gpr = s.gpr ∧ Rest [] s s' := by
  unfold storeN
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun m s' => (∀ j < m, wd s'.mem (State.addr b) (o + 4 * j) = (s.gpr r).toNat) ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 o, 4 * m⟩] s.mem s'.mem ∧ s'.gpr = s.gpr ∧ Rest [] s s')
    (fun m s' hm ⟨h1, h2, h3, h4⟩ => ?_) n (Nat.le_refl _) s
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), Frame.refl _ _, rfl, Rest.refl _ _⟩) fun s' h => h
  refine VG.Proof.X25519.Arm.str0_ok (hc.of_rest h4 (by decide)) (d := o + 4 * m) (by omega) fun s2 u2 =>
    WP.block_nil ⟨fun j hj => ?_, ?_, by rw [u2.gpr, h3], h4.trans (u2.rest _)⟩
  · rw [u2.mem]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [wd_write_other _ _ _ (by omega) (by omega) (by omega)]; exact h1 j hj
    · rw [wd_write_self, h3]
  · rw [u2.mem]
    exact (h2.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega)⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains _ (by omega) (by omega) (by omega))

/-! ## The inversion -/

/-- The slots of the inversion. -/
def IQ : List Nat := [Z2, R, X2]

/-- `z^((p - 2) >> n)` in `R`, for `z` at `Z2`. -/
def invV (v : Nat → Fe) (n : Nat) : Nat → Fe := VG.Proof.X25519.Arm.upd v R (VG.Proof.X25519.pw (v Z2) ((P - 2) >>> n))

/-- The loop invariant of the inversion from `sI`, before the step for the bit
`n - 1`. -/
structure InvInv (b : BitVec 32) (sI : State) (c : BitVec 32) (v : Nat → Fe) (n : Nat) (s : State) :
    Prop where
  cur : VG.Proof.X25519.Arm.Cur b sI (BitVec.ofNat 32 n) c VG.Proof.X25519.Arm.IQ (VG.Proof.X25519.Arm.invV v n) s

theorem sub_beq {x y : Nat} (hx : x < 2 ^ 32) (hy : y < 2 ^ 32) :
    (BitVec.ofNat 32 x - BitVec.ofNat 32 y == 0) = decide (x = y) := by
  by_cases h : x = y
  · subst h; simp
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    apply h
    have e : BitVec.ofNat 32 x = BitVec.ofNat 32 y := by
      rw [← BitVec.sub_add_cancel (BitVec.ofNat 32 x) (BitVec.ofNat 32 y), h']; simp
    have := congrArg BitVec.toNat e
    rwa [toNat_imm hx, toNat_imm hy] at this

theorem Cur.congr {s0 s : State} {a c : BitVec 32} {qs qs' : List Nat} {v w : Nat → Fe}
    (h : VG.Proof.X25519.Arm.Cur b s0 a c qs v s) (hq : ∀ q ∈ qs', q ∈ qs) (hv : ∀ q ∈ qs', v q = w q) : VG.Proof.X25519.Arm.Cur b s0 a c qs' w s :=
  ⟨h.ctx, h.stp, h.r10, h.r11, (h.slots.mono hq).congr hv⟩

theorem invStep_ok {sI : State} {c : BitVec 32} {v : Nat → Fe} {n : Nat} (hn : 1 ≤ n) (hn' : n ≤ 255)
    {s : State} (h : VG.Proof.X25519.Arm.InvInv b sI c v n s) :
    WP isa invStep s fun s' => VG.Proof.X25519.Arm.InvInv b sI c v (n - 1) s' ∧ s'.z = decide (n - 1 = 0) := by
  obtain ⟨hcur⟩ := h
  have hb := VG.Proof.X25519.Arm.pbits (n - 1) (by omega)
  have he := VG.Proof.X25519.Arm.shr_step (P - 2) (n - 1)
  rw [Nat.sub_add_cancel hn] at he
  unfold invStep
  refine WP.seq (wp_dp (op2_imm (by decide)) fun s1 u1 => WP.block_nil ?_)
  have h1 : VG.Proof.X25519.Arm.Cur b sI (BitVec.ofNat 32 (n - 1)) c VG.Proof.X25519.Arm.IQ (VG.Proof.X25519.Arm.invV v n) s1 := by
    refine ⟨hcur.ctx.of_rest (u1.rest (ws := [.r10]) (by decide)) (by decide),
      hcur.stp.trans (Stp.of_rest (u1.rest (ws := [.r10]) (by decide)) (by decide) u1.mem), ?_,
      by rw [u1.other _ (by decide), hcur.r11], by rw [u1.mem]; exact hcur.slots⟩
    rw [u1.gpr]; show s.gpr .r10 - 1 = _
    rw [hcur.r10]
    apply BitVec.eq_of_toNat_eq
    have t1 : (1 : BitVec 32).toNat = 1 := rfl
    rw [toNat_sub_le (by rw [toNat_imm (by omega), t1]; omega), toNat_imm (by omega), toNat_imm (by omega), t1]
  refine WP.seq (WP.mono (VG.Proof.X25519.Arm.opMul (o := R) (x := R) (y := R) (by decide) (by decide) (by decide) (by decide) h1)
    fun s2 h2 => ?_)
  -- After the square.
  have hsq : ∀ q ∈ VG.Proof.X25519.Arm.IQ, VG.Proof.X25519.Arm.upd (VG.Proof.X25519.Arm.invV v n) R (VG.Proof.X25519.Arm.invV v n R * VG.Proof.X25519.Arm.invV v n R) q =
      VG.Proof.X25519.Arm.upd v R (VG.Proof.X25519.pw (v Z2) (2 * ((P - 2) >>> n))) q := by
    intro q _
    by_cases hq : q = R
    · subst hq; rw [VG.Proof.X25519.Arm.upd_self, VG.Proof.X25519.Arm.invV, VG.Proof.X25519.Arm.upd_self, VG.Proof.X25519.Arm.upd_self, Nat.two_mul, ← VG.Proof.X25519.pw_mul]
    · rw [VG.Proof.X25519.Arm.upd_of_ne _ _ hq, VG.Proof.X25519.Arm.invV, VG.Proof.X25519.Arm.upd_of_ne _ _ hq, VG.Proof.X25519.Arm.upd_of_ne _ _ hq]
  have h2' := h2.congr (qs' := VG.Proof.X25519.Arm.IQ) (by decide) hsq
  refine WP.seq (wp_cmp (op2_imm (by decide)) fun s3 u3 hz3 => WP.block_nil ?_)
  have h3 := h2'.next (Fupd.rest u3 _) (by rw [u3.mem]; exact Frame.refl _ _) (by rw [u3.mem]; exact h2'.slots)
  have hz3' : s3.z = decide (n - 1 = 4) := by
    rw [hz3, h2'.r10]; exact VG.Proof.X25519.Arm.sub_beq (by omega) (by decide)
  refine WP.seq (WP.mono (Q := VG.Proof.X25519.Arm.Cur b sI (BitVec.ofNat 32 (n - 1)) c VG.Proof.X25519.Arm.IQ (VG.Proof.X25519.Arm.invV v (n - 1))) ?_ fun s4 h4 =>
    wp_cmp (op2_imm (by decide)) fun s5 u5 hz5 => WP.block_nil ⟨⟨h4.next (Fupd.rest u5 _)
      (by rw [u5.mem]; exact Frame.refl _ _) (by rw [u5.mem]; exact h4.slots)⟩, ?_⟩)
  · refine WP.ite s3.z (eval_eq _) (fun ht => WP.block_nil (h3.congr (fun q hq => hq) fun q _ => ?_))
      (fun hf => ?_)
    · have h4 : n - 1 = 4 := by rw [hz3'] at ht; simpa using ht
      by_cases hq : q = R
      · subst hq; rw [VG.Proof.X25519.Arm.upd_self, VG.Proof.X25519.Arm.invV, VG.Proof.X25519.Arm.upd_self, he, hb, VG.Proof.X25519.Arm.iteT (.inl h4), Nat.add_zero]
      · rw [VG.Proof.X25519.Arm.upd_of_ne _ _ hq, VG.Proof.X25519.Arm.invV, VG.Proof.X25519.Arm.upd_of_ne _ _ hq]
    · have h4 : n - 1 ≠ 4 := by rw [hz3'] at hf; simpa using hf
      refine WP.seq (wp_cmp (op2_imm (by decide)) fun s4 u4 hz4 => WP.block_nil ?_)
      have h4' := h3.next (Fupd.rest u4 _) (by rw [u4.mem]; exact Frame.refl _ _) (by rw [u4.mem]; exact h3.slots)
      have hz4' : s4.z = decide (n - 1 = 2) := by
        rw [hz4, h3.r10]; exact VG.Proof.X25519.Arm.sub_beq (by omega) (by decide)
      refine WP.ite s4.z (eval_eq _) (fun ht => WP.block_nil (h4'.congr (fun q hq => hq) fun q _ => ?_))
        (fun hf => ?_)
      · have h2 : n - 1 = 2 := by rw [hz4'] at ht; simpa using ht
        by_cases hq : q = R
        · subst hq; rw [VG.Proof.X25519.Arm.upd_self, VG.Proof.X25519.Arm.invV, VG.Proof.X25519.Arm.upd_self, he, hb, VG.Proof.X25519.Arm.iteT (.inr h2), Nat.add_zero]
        · rw [VG.Proof.X25519.Arm.upd_of_ne _ _ hq, VG.Proof.X25519.Arm.invV, VG.Proof.X25519.Arm.upd_of_ne _ _ hq]
      · have h2 : n - 1 ≠ 2 := by rw [hz4'] at hf; simpa using hf
        refine WP.mono (VG.Proof.X25519.Arm.opMul (o := R) (x := R) (y := Z2) (by decide) (by decide) (by decide) (by decide) h4')
          fun s5 h5 => h5.congr (by decide) fun q _ => ?_
        by_cases hq : q = R
        · subst hq
          rw [VG.Proof.X25519.Arm.upd_self, VG.Proof.X25519.Arm.upd_self, VG.Proof.X25519.Arm.upd_of_ne _ _ (by decide : Z2 ≠ R), VG.Proof.X25519.Arm.invV, VG.Proof.X25519.Arm.upd_self, he, hb,
            VG.Proof.X25519.Arm.iteF (show ¬ (n - 1 = 4 ∨ n - 1 = 2) by omega), ← VG.Proof.X25519.pw_mul,
            VG.Proof.X25519.pw_one]
        · rw [VG.Proof.X25519.Arm.upd_of_ne _ _ hq, VG.Proof.X25519.Arm.upd_of_ne _ _ hq, VG.Proof.X25519.Arm.invV, VG.Proof.X25519.Arm.upd_of_ne _ _ hq]
  · rw [hz5, h4.r10]; exact VG.Proof.X25519.Arm.sub_beq (by omega) (by decide)

theorem invert_ok {c : BitVec 32} {v : Nat → Fe} {s : State} (hc : VG.Proof.X25519.Arm.Ctx b s)
    (hS : VG.Proof.X25519.Arm.SlotsOk s.mem (State.addr b) [Z2, X2] v) (h11 : s.gpr .r11 = c) :
    WP isa Impl.X25519.Arm.invert s fun s' => VG.Proof.X25519.Arm.Stp b s s' ∧ VG.Proof.X25519.Arm.Ctx b s' ∧
      VG.Proof.X25519.Arm.SlotsOk s'.mem (State.addr b) VG.Proof.X25519.Arm.IQ (VG.Proof.X25519.Arm.upd v R (VG.Proof.X25519.pw (v Z2) (P - 2))) := by
  unfold Impl.X25519.Arm.invert
  refine WP.seq ?_
  simp only [one, List.cons_append, List.nil_append]
  refine wp_mov (op2_imm (by decide)) fun s1 u1 => wp_mov (op2_imm (by decide)) fun s2 u2 => ?_
  have hr2 : Rest [.r1, .r2] s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  have hc2 : VG.Proof.X25519.Arm.Ctx b s2 := hc.of_rest hr2 (by decide)
  refine VG.Proof.X25519.Arm.str0_ok hc2 (d := R) (by decide) fun s3 u3 => ?_
  refine WP.append (VG.Proof.X25519.Arm.stores_ok (o := R + 4) (n := 15) (by decide) (hc2.of_rest (u3.rest []) (by decide)))
    fun s4 ⟨h4w, h4f, h4g, h4r⟩ => ?_
  refine wp_mov (op2_imm (by decide)) fun s5 u5 => WP.block_nil ?_
  have hr5 : Rest [.r1, .r2, .r10] s s5 :=
    (hr2.mono (by decide)).trans ((u3.rest _).trans ((h4r.mono (by decide)).trans (u5.rest (by decide))))
  have hm2 : s2.mem = s.mem := by rw [u2.mem, u1.mem]
  -- The limbs of `R`: 1, then zeros.
  have hlimb : ∀ k < 16, VG.Proof.X25519.Arm.limb s5.mem (State.addr b) R k = if k = 0 then 1 else 0 := by
    intro k hk
    rw [VG.Proof.X25519.Arm.limb, u5.mem]
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [Nat.mul_zero, Nat.add_zero, wd_frame h4f fun r hr => by
        rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide),
        u3.mem, wd_write_self, u2.other _ (by decide), u1.gpr]; rfl
    · have := h4w (k - 1) (by omega)
      rw [show R + 4 + 4 * (k - 1) = R + 4 * k by omega, u3.gpr, u2.gpr] at this
      rw [this]; simp only [show k ≠ 0 by omega, ite_false]; rfl
  have hf5 : Frame [⟨State.addr b + BitVec.ofNat 64 R, 64⟩] s.mem s5.mem := by
    rw [u5.mem, ← hm2]
    refine ((Frame.refl _ _).writeW (List.mem_singleton_self _) (s2.gpr .r1)
      (Offset.contains (State.addr b) (d := R) (n := 4) (e := R) (k := 64) (Nat.le_refl _) (by decide)
        (by decide))).trans ?_
    rw [← u3.mem]
    exact h4f.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by decide) (by decide)⟩
  have hc5 : VG.Proof.X25519.Arm.Ctx b s5 := hc.of_rest hr5 (by decide)
  have hst5 : VG.Proof.X25519.Arm.Stp b s s5 := ⟨hr5.mono (by decide), hf5.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by decide) (by decide)⟩⟩
  have hS5 : VG.Proof.X25519.Arm.SlotsOk s5.mem (State.addr b) VG.Proof.X25519.Arm.IQ (VG.Proof.X25519.Arm.invV v 255) := by
    have hZ2 : Z2 = 192 := rfl
    have hX2 : X2 = 128 := rfl
    have hR : R = 1024 := rfl
    intro q hq
    simp only [VG.Proof.X25519.Arm.IQ, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · have e := VG.Proof.X25519.Arm.limb_frame (o := Z2) hf5 fun r hr k hk => by
        rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
      refine ⟨fun k hk => by rw [e k hk]; exact (hS Z2 (by decide)).1 k hk, ?_⟩
      rw [VG.Proof.X25519.Arm.FS, VG.Proof.X25519.Arm.V, val16_congr e, VG.Proof.X25519.Arm.invV, VG.Proof.X25519.Arm.upd_of_ne _ _ (by decide)]; exact (hS Z2 (by decide)).2
    · refine ⟨fun k hk => by rw [hlimb k hk]; split <;> decide, ?_⟩
      rw [VG.Proof.X25519.Arm.FS, VG.Proof.X25519.Arm.V, val16_congr hlimb, VG.Proof.X25519.Arm.invV, VG.Proof.X25519.Arm.upd_self, VG.Proof.X25519.Arm.p255, VG.Proof.X25519.pw_zero]
      rfl
    · have e := VG.Proof.X25519.Arm.limb_frame (o := X2) hf5 fun r hr k hk => by
        rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
      refine ⟨fun k hk => by rw [e k hk]; exact (hS X2 (by decide)).1 k hk, ?_⟩
      rw [VG.Proof.X25519.Arm.FS, VG.Proof.X25519.Arm.V, val16_congr e, VG.Proof.X25519.Arm.invV, VG.Proof.X25519.Arm.upd_of_ne _ _ (by decide)]; exact (hS X2 (by decide)).2
  have h255 : VG.Proof.X25519.Arm.InvInv b s5 c v 255 s5 :=
    ⟨⟨hc5, Stp.refl _ _, u5.gpr, by rw [hr5.gpr _ (by decide), h11], hS5⟩⟩
  refine WP.mono (Q := VG.Proof.X25519.Arm.InvInv b s5 c v 0) (WP.loop (M := isa)
    (fun m s' => 1 ≤ m ∧ m ≤ 255 ∧ VG.Proof.X25519.Arm.InvInv b s5 c v m s') ?_ 255 s5 ⟨by decide, Nat.le_refl _, h255⟩)
    fun s' ⟨h'⟩ => ⟨hst5.trans h'.stp, h'.ctx, h'.slots.congr fun q _ => by
      simp only [VG.Proof.X25519.Arm.invV, Nat.shiftRight_zero]⟩
  rintro m s' ⟨h1, h2, hl⟩
  refine WP.mono (VG.Proof.X25519.Arm.invStep_ok h1 h2 hl) fun s'' ⟨hl', hz⟩ => ?_
  by_cases hm : m - 1 = 0
  · exact .inl ⟨by rw [eval_ne, hz]; simp [hm], by rw [hm] at hl'; exact hl'⟩
  · exact .inr ⟨by rw [eval_ne, hz]; simp [hm], m - 1, by omega, by omega, by omega, hl'⟩

end

end VG.Proof.X25519.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.Arm.Freeze`. -/
section

/-!
# X25519 on 32-bit ARM: the final reduction and the output

`freeze` stores the 32 bytes of the element at `X2`, reduced fully modulo `p`,
at `out` (`freeze_ok`).
-/

namespace VG.Proof.X25519.Arm

open VG VG.Arm VG.Impl.X25519.Arm
open VG.Spec.X25519 (P Fe bytesAt)
open VG.Proof.X25519 (leBytes)

theorem low15_val (x : BitVec 32) : ((x <<< 17) >>> 17).toNat = x.toNat % 32768 := by
  rw [toNat_shr, toNat_shl, show (2 : Nat) ^ 32 = 32768 * 2 ^ 17 from rfl, Nat.mul_mod_mul_right,
    Nat.mul_div_cancel _ (Nat.two_pow_pos _)]

theorem sel0r (a c : BitVec 32) : a ^^^ ((c ^^^ a) &&& (0 - BitVec.ofNat 32 0)) = a := by simp

theorem sel1r (a c : BitVec 32) : a ^^^ ((c ^^^ a) &&& (0 - BitVec.ofNat 32 1)) = c := by
  have : (0 : BitVec 32) - BitVec.ofNat 32 1 = BitVec.allOnes 32 := by decide
  rw [this, BitVec.and_allOnes, BitVec.xor_comm c, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

theorem byte_eq {v : BitVec 32} {n : Nat} (h : v.toNat = n) : v.setWidth 8 = BitVec.ofNat 8 n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, h]

theorem ofNat8_eq {a c : Nat} (h : a % 256 = c % 256) : BitVec.ofNat 8 a = BitVec.ofNat 8 c := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]; exact h

/-- The bytes at `O` are those of `X`, if the bytes `2k` and `2k + 1` are those
of limb `k`. -/
theorem bytesAt_limbs {m : Mem} {O : Addr} {r : Nat → Nat} (hr : ∀ k < 16, r k < 65536)
    (h0 : ∀ k < 16, m (O + BitVec.ofNat 64 (2 * k)) = BitVec.ofNat 8 (r k))
    (h1 : ∀ k < 16, m (O + BitVec.ofNat 64 (2 * k + 1)) = BitVec.ofNat 8 (r k / 256)) :
    bytesAt m O 32 = leBytes 32 (val16 r 16) := by
  simp only [bytesAt, leBytes]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  have hk : i / 2 < 16 := by omega
  obtain ⟨b0, b1⟩ := bytes_of_limbs hr hk
  rcases Nat.mod_two_eq_zero_or_one i with he | ho
  · rw [show i = 2 * (i / 2) by omega, h0 _ hk]
    exact VG.Proof.X25519.Arm.ofNat8_eq b0.symm
  · rw [show i = 2 * (i / 2) + 1 by omega, h1 _ hk]
    refine VG.Proof.X25519.Arm.ofNat8_eq ?_
    rw [b1, Nat.mod_eq_of_lt (by have := hr _ hk; omega)]

section
variable {b : BitVec 32}

/-- The start of `freeze`: bit 255 of `[X2]` cleared, 19 times it in `r5`. -/
theorem freezeA_ok {s : State} (hc : VG.Proof.X25519.Arm.Ctx b s) (hl : VG.Proof.X25519.Arm.Lim s.mem (State.addr b) X2) :
    WP isa (.block freezeA) s fun s' =>
      s'.gpr .r6 = mask16 ∧ (s'.gpr .r5).toNat = 19 * (VG.Proof.X25519.Arm.limb s.mem (State.addr b) X2 15 / 32768) ∧
      (∀ k < 16, VG.Proof.X25519.Arm.limb s'.mem (State.addr b) X2 k = mask15 (VG.Proof.X25519.Arm.limb s.mem (State.addr b) X2) k) ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 X2, 64⟩] s.mem s'.mem ∧
      Rest [.r2, .r3, .r5, .r6] s s' := by
  have hX : X2 = 128 := rfl
  simp only [freezeA, low15, List.cons_append, List.nil_append]
  refine wp_movw fun s1 u1 => ?_
  have hc1 : VG.Proof.X25519.Arm.Ctx b s1 := hc.of_rest (u1.rest (ws := [.r6]) (by decide)) (by decide)
  refine VG.Proof.X25519.Arm.ldr0_ok hc1 (d := X2 + 60) (by decide) fun s2 u2 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s3 u3 => wp_mov (op2_lsl (by decide)) fun s4 u4 =>
    wp_mov (op2_lsr (by decide)) fun s5 u5 => ?_
  have hr5 : Rest [.r3, .r5, .r6] s s5 :=
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
      ((u4.rest (by decide)).trans (u5.rest (by decide)))))
  have hc5 : VG.Proof.X25519.Arm.Ctx b s5 := hc.of_rest hr5 (by decide)
  refine VG.Proof.X25519.Arm.str0_ok hc5 (d := X2 + 60) (by decide) fun s6 u6 => ?_
  refine wp_mov (op2_imm (by decide)) fun s7 u7 => wp_mul fun s8 u8 => WP.block_nil ?_
  have hl15 := hl 15 (by decide)
  have e2 : (s2.gpr .r3).toNat = VG.Proof.X25519.Arm.limb s.mem (State.addr b) X2 15 := by rw [u2.gpr, u1.mem]; rfl
  have e5 : (s5.gpr .r3).toNat = VG.Proof.X25519.Arm.limb s.mem (State.addr b) X2 15 % 32768 := by
    rw [u5.gpr, u4.gpr, VG.Proof.X25519.Arm.low15_val, u3.other .r3 (by decide), e2]
  have e3 : (s3.gpr .r5).toNat = VG.Proof.X25519.Arm.limb s.mem (State.addr b) X2 15 / 32768 := by
    rw [u3.gpr, toNat_shr, e2]
  have hm6 : s6.mem = s.mem.writeW (State.addr b + BitVec.ofNat 64 (X2 + 60)) (s5.gpr .r3) := by
    rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  refine ⟨?_, ?_, fun k hk => ?_, ?_, ?_⟩
  · rw [u8.other _ (by decide), u7.other _ (by decide), u6.gpr, u5.other .r6 (by decide),
      u4.other .r6 (by decide), u3.other .r6 (by decide), u2.other .r6 (by decide), u1.gpr]
  · rw [u8.gpr, u7.other _ (by decide), u7.gpr, u6.gpr, u5.other _ (by decide), u4.other _ (by decide),
      toNat_mul_lt (by rw [e3]; show _ * 19 < _; omega), e3]
    show _ * 19 = _
    omega
  · rw [VG.Proof.X25519.Arm.limb, u8.mem, u7.mem, hm6]
    rcases Nat.lt_or_ge k 15 with h | h
    · rw [wd_write_other _ _ _ (by omega) (by omega) (by omega)]
      simp only [mask15, show k ≠ 15 by omega, ite_false]; rfl
    · rw [show X2 + 4 * k = X2 + 60 by omega, wd_write_self, e5, show k = 15 by omega]; rfl
  · rw [u8.mem, u7.mem, hm6]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains _ (d := X2 + 60) (n := 4) (Nat.le_add_right _ _) (by omega) (by omega))
  · exact (hr5.mono (by decide)).trans ((u6.rest _).trans ((u7.rest (by decide)).trans (u8.rest (by decide))))

/-- `freezeB`: the mask `-(bit 255 of [Y])` in `r9`, and bit 255 of `[Y]` cleared. -/
theorem freezeB_ok {s : State} (hc : VG.Proof.X25519.Arm.Ctx b s) :
    WP isa (.block freezeB) s fun s' =>
      s'.gpr .r9 = 0 - BitVec.ofNat 32 (VG.Proof.X25519.Arm.limb s.mem (State.addr b) Y 15 / 32768) ∧
      (∀ k < 16, VG.Proof.X25519.Arm.limb s'.mem (State.addr b) Y k = mask15 (VG.Proof.X25519.Arm.limb s.mem (State.addr b) Y) k) ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 Y, 64⟩] s.mem s'.mem ∧ Rest [.r1, .r3, .r9] s s' := by
  have hY : Y = 1088 := rfl
  simp only [freezeB, low15, List.cons_append, List.nil_append]
  refine VG.Proof.X25519.Arm.ldr0_ok hc (d := Y + 60) (by decide) fun s1 u1 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s2 u2 => wp_mov (op2_imm (by decide)) fun s3 u3 =>
    wp_dp (op2_reg _ _) fun s4 u4 => wp_mov (op2_lsl (by decide)) fun s5 u5 =>
    wp_mov (op2_lsr (by decide)) fun s6 u6 => ?_
  have hr6 : Rest [.r1, .r3, .r9] s s6 :=
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
      ((u4.rest (by decide)).trans ((u5.rest (by decide)).trans (u6.rest (by decide))))))
  refine VG.Proof.X25519.Arm.str0_ok (hc.of_rest hr6 (by decide)) (d := Y + 60) (by decide) fun s7 u7 => WP.block_nil ?_
  have e1 : (s1.gpr .r3).toNat = VG.Proof.X25519.Arm.limb s.mem (State.addr b) Y 15 := by rw [u1.gpr]; rfl
  have hm7 : s7.mem = s.mem.writeW (State.addr b + BitVec.ofNat 64 (Y + 60)) (s6.gpr .r3) := by
    rw [u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  refine ⟨?_, fun k hk => ?_, ?_, hr6.trans (u7.rest _)⟩
  · rw [u7.gpr, u6.other _ (by decide), u5.other _ (by decide), u4.gpr]
    show s3.gpr .r1 - s3.gpr .r9 = _
    rw [u3.gpr, u3.other _ (by decide), u2.gpr]
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [toNat_shr, e1, toNat_imm (by have := wd_lt s.mem (State.addr b) (Y + 4 * 15); unfold VG.Proof.X25519.Arm.limb; omega)]
  · rw [VG.Proof.X25519.Arm.limb, hm7]
    rcases Nat.lt_or_ge k 15 with h | h
    · rw [wd_write_other _ _ _ (by omega) (by omega) (by omega)]
      simp only [mask15, show k ≠ 15 by omega, ite_false]; rfl
    · rw [show Y + 4 * k = Y + 60 by omega, wd_write_self, u6.gpr, u5.gpr, VG.Proof.X25519.Arm.low15_val, u4.other .r3 (by decide),
        u3.other .r3 (by decide), u2.other .r3 (by decide), e1, show k = 15 by omega]; rfl
  · rw [hm7]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains _ (d := Y + 60) (n := 4) (Nat.le_add_right _ _) (by omega) (by omega))

/-- The output of `freeze` from `s0`, after `j` limbs. -/
structure OutInv (O : Addr) (r : Nat → Nat) (s0 : State) (j : Nat) (s : State) : Prop where
  rest : Rest [.r2, .r3] s0 s
  frame : Frame [⟨O, 2 * j⟩] s0.mem s.mem
  b0 : ∀ i < j, s.mem (O + BitVec.ofNat 64 (2 * i)) = BitVec.ofNat 8 (r i)
  b1 : ∀ i < j, s.mem (O + BitVec.ofNat 64 (2 * i + 1)) = BitVec.ofNat 8 (r i / 256)

theorem out_ok {s0 : State} (hc : VG.Proof.X25519.Arm.Ctx b s0) {o : BitVec 32} (h12 : s0.gpr .r12 = o)
    (hout : (⟨State.addr o, 32⟩ : Region) ∈ s0.wr) (hofit : o.toNat + 32 ≤ 2 ^ 32)
    (hdisj : Region.Disjoint ⟨State.addr b, 4096⟩ ⟨State.addr o, 32⟩) {sw : Nat} (hsw : sw ≤ 1)
    (h9 : s0.gpr .r9 = 0 - BitVec.ofNat 32 sw) :
    WP isa (.block ((List.range 16).flatMap outStep)) s0
      (VG.Proof.X25519.Arm.OutInv (State.addr o) (fun k => sel sw (VG.Proof.X25519.Arm.limb s0.mem (State.addr b) X2 k)
        (VG.Proof.X25519.Arm.limb s0.mem (State.addr b) Y k)) s0 16) := by
  have hX : X2 = 128 := rfl
  have hY : Y = 1088 := rfl
  refine wp_range_flatMap (M := isa) _ (fun k s hk h => ?_) 16 (Nat.le_refl _) s0
    ⟨Rest.refl _ _, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _),
      fun _ h => absurd h (Nat.not_lt_zero _)⟩
  have hcs : VG.Proof.X25519.Arm.Ctx b s := hc.of_rest h.rest (by decide)
  -- The words of the working space are as in `s0`.
  have hw : ∀ d, d + 4 ≤ 4096 → wd s.mem (State.addr b) d = wd s0.mem (State.addr b) d := fun d hd =>
    wd_frame h.frame fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact (hdisj.sub_left (Offset.sub_base _ hd)).sub_right (Region.sub_prefix (by omega))
  unfold outStep
  refine VG.Proof.X25519.Arm.ldr0_ok hcs (d := X2 + 4 * k) (by omega) fun t1 v1 => ?_
  refine VG.Proof.X25519.Arm.ldr0_ok (hcs.of_rest (v1.rest (ws := [.r2]) (by decide)) (by decide)) (d := Y + 4 * k) (by omega)
    fun t2 v2 => ?_
  refine wp_dp (op2_reg _ _) fun t3 v3 => wp_dp (op2_reg _ _) fun t4 v4 =>
    wp_dp (op2_reg _ _) fun t5 v5 => ?_
  have hr5 : Rest [.r2, .r3] s t5 :=
    (v1.rest (by decide)).trans ((v2.rest (by decide)).trans ((v3.rest (by decide)).trans
      ((v4.rest (by decide)).trans (v5.rest (by decide)))))
  have e12 : t5.gpr .r12 = o := by rw [hr5.gpr _ (by decide), h.rest.gpr _ (by decide), h12]
  have hwr : t5.wr = s0.wr := by rw [hr5.wr, h.rest.wr]
  refine wp_strb (a := State.addr o + BitVec.ofNat 64 (2 * k)) (by omega)
    (by rw [e12]; exact addr_add (by omega)) (by rw [hwr]; exact in_base hout (by omega) (by omega))
    fun t6 v6 => ?_
  refine wp_mov (op2_lsr (by decide)) fun t7 v7 => ?_
  refine wp_strb (a := State.addr o + BitVec.ofNat 64 (2 * k + 1)) (by omega)
    (by rw [v7.other _ (by decide), v6.gpr, e12]; exact addr_add (by omega))
    (by rw [v7.wr, v6.wr, hwr]; exact in_base hout (by omega) (by omega)) fun t8 v8 => WP.block_nil ?_
  -- The limb selected.
  have ev : (t5.gpr .r2).toNat = sel sw (VG.Proof.X25519.Arm.limb s0.mem (State.addr b) X2 k) (VG.Proof.X25519.Arm.limb s0.mem (State.addr b) Y k) := by
    have ex : t2.gpr .r2 = s.mem.readW (State.addr b + BitVec.ofNat 64 (X2 + 4 * k)) 32 := by
      rw [v2.other _ (by decide), v1.gpr]
    have ey : t2.gpr .r3 = s.mem.readW (State.addr b + BitVec.ofNat 64 (Y + 4 * k)) 32 := by
      rw [v2.gpr, v1.mem]
    have em : t3.gpr .r9 = 0 - BitVec.ofNat 32 sw := by
      rw [v3.other _ (by decide), v2.other _ (by decide), v1.other _ (by decide), h.rest.gpr _ (by decide), h9]
    rw [v5.gpr]
    show (t4.gpr .r2 ^^^ t4.gpr .r3).toNat = _
    rw [v4.other .r2 (by decide), v4.gpr]
    show (t3.gpr .r2 ^^^ (t3.gpr .r3 &&& t3.gpr .r9)).toNat = _
    rw [v3.other .r2 (by decide), v3.gpr, em]
    show (t2.gpr .r2 ^^^ ((t2.gpr .r3 ^^^ t2.gpr .r2) &&& _)).toNat = _
    rw [ex, ey]
    have hx := hw (X2 + 4 * k) (by omega)
    have hy := hw (Y + 4 * k) (by omega)
    unfold wd at hx hy
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsw with rfl | rfl
    · rw [VG.Proof.X25519.Arm.sel0r, hx]; rfl
    · rw [VG.Proof.X25519.Arm.sel1r, hy]; rfl
  have hm8 : t8.mem = (s.mem.writeW (State.addr o + BitVec.ofNat 64 (2 * k)) ((t5.gpr .r2).setWidth 8)).writeW
      (State.addr o + BitVec.ofNat 64 (2 * k + 1)) ((t5.gpr .r2 >>> 8).setWidth 8) := by
    rw [v8.mem, v7.gpr, v7.mem, v6.gpr, v6.mem, v5.mem, v4.mem, v3.mem, v2.mem, v1.mem]
  have ne : ∀ a c : Nat, a < 32 → c < 32 → a ≠ c →
      State.addr o + BitVec.ofNat 64 a ≠ State.addr o + BitVec.ofNat 64 c :=
    fun a c ha hc' hac => Offset.add_ofNat_ne _ (by omega) (by omega) hac
  refine ⟨h.rest.trans (hr5.trans ((v6.rest _).trans ((v7.rest (by decide)).trans (v8.rest _)))), ?_,
    fun i hi => ?_, fun i hi => ?_⟩
  · rw [hm8]
    refine ((h.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega)⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
  · rw [hm8, VG.WriteBytes.writeW8_apply, VG.WriteBytes.writeW8_apply,
      VG.Proof.X25519.Arm.iteF (ne _ _ (by omega) (by omega) (by omega))]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [VG.Proof.X25519.Arm.iteF (ne _ _ (by omega) (by omega) (by omega))]; exact h.b0 i hi
    · rw [VG.Proof.X25519.Arm.iteT rfl]; exact VG.Proof.X25519.Arm.byte_eq ev
  · rw [hm8, VG.WriteBytes.writeW8_apply, VG.WriteBytes.writeW8_apply]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [VG.Proof.X25519.Arm.iteF (ne _ _ (by omega) (by omega) (by omega)), VG.Proof.X25519.Arm.iteF (ne _ _ (by omega) (by omega) (by omega))]
      exact h.b1 i hi
    · rw [VG.Proof.X25519.Arm.iteT rfl]
      exact VG.Proof.X25519.Arm.byte_eq (by rw [toNat_shr, ev])

theorem frame_sub1 {m m' : Mem} {r r' : Region} {rs : List Region} (h : Frame [r] m m') (hs : Region.Sub r r')
    (hr : r' ∈ rs) : Frame rs m m' :=
  h.sub fun x hx => ⟨r', hr, by rw [List.mem_singleton.mp hx]; exact hs⟩

theorem freeze_ok {s : State} (hc : VG.Proof.X25519.Arm.Ctx b s) (hl : VG.Proof.X25519.Arm.Lim s.mem (State.addr b) X2) {o : BitVec 32}
    (h12 : s.gpr .r12 = o) (hout : (⟨State.addr o, 32⟩ : Region) ∈ s.wr) (hofit : o.toNat + 32 ≤ 2 ^ 32)
    (hdisj : Region.Disjoint ⟨State.addr b, 4096⟩ ⟨State.addr o, 32⟩) :
    WP isa (.block freeze) s fun s' =>
      bytesAt s'.mem (State.addr o) 32 = leBytes 32 (VG.Proof.X25519.Arm.V s.mem (State.addr b) X2 % P) ∧ Rest VG.Proof.X25519.Arm.clob s s' ∧
      Frame [VG.Proof.X25519.Arm.FA ACC b, ⟨State.addr o, 32⟩] s.mem s'.mem := by
  have hX : X2 = 128 := rfl
  have hY : Y = 1088 := rfl
  obtain ⟨tA, tY, hS, hR, hv⟩ := freeze_facts hl
  obtain ⟨-, -, lm, c1⟩ := mask15_facts hl
  simp only [freeze, List.append_assoc, List.cons_append, List.nil_append]
  refine WP.append (VG.Proof.X25519.Arm.freezeA_ok hc hl) fun s1 ⟨h6, h5, hl1, hf1, hr1⟩ => ?_
  have hc1 : VG.Proof.X25519.Arm.Ctx b s1 := hc.of_rest hr1 (by decide)
  refine WP.append (VG.Proof.X25519.Arm.pass_ok (rb := .r0) (o := X2) (s0 := s1) (c := mask15 (VG.Proof.X25519.Arm.limb s.mem (State.addr b) X2))
    (cin := 19 * (VG.Proof.X25519.Arm.limb s.mem (State.addr b) X2 15 / 32768)) (by decide) (by decide)
    (by rw [hc1.r0]; have := hc.fit; omega) (fun k hk => by rw [hc1.r0]; exact hc1.inW (by omega)) h6 h5
    (fun k hk => by have := lm k hk; omega) (by omega) ?_) fun s2 hp2 => ?_
  · intro k hk s' hp
    refine WP.mono (VG.Proof.X25519.Arm.ldSrc_ok (hc1.of_rest hp.rest (by decide)) (o := X2) (k := k) (by omega)) fun t ht => ⟨?_, ht.2.1.mono (by decide), ht.2.2⟩
    rw [ht.1, VG.Proof.X25519.Arm.wd_pass hc1 hp.frame (by omega) (by omega) (by omega)]
    exact hl1 k hk
  have hc2 : VG.Proof.X25519.Arm.Ctx b s2 := hc1.of_rest hp2.rest (by decide)
  have hpo2 : ∀ j < 16, wd s2.mem (State.addr b) (X2 + 4 * j) = frA (VG.Proof.X25519.Arm.limb s.mem (State.addr b) X2) j :=
    fun j hj => by have := hp2.outs j hj; rwa [hc1.r0] at this
  have hpf2 : Frame [⟨State.addr b + BitVec.ofNat 64 X2, 64⟩] s1.mem s2.mem := by
    have := hp2.frame; rwa [hc1.r0] at this
  refine wp_mov (op2_imm (by decide)) fun s3 u3 => ?_
  have hc3 : VG.Proof.X25519.Arm.Ctx b s3 := hc2.of_rest (u3.rest (ws := [.r5]) (by decide)) (by decide)
  refine WP.append (VG.Proof.X25519.Arm.pass_ok (rb := .r0) (o := Y) (s0 := s3) (c := frA (VG.Proof.X25519.Arm.limb s.mem (State.addr b) X2))
    (cin := 19) (by decide) (by decide)
    (by rw [hc3.r0]; have := hc.fit; omega) (fun k hk => by rw [hc3.r0]; exact hc3.inW (by omega))
    (by rw [u3.other _ (by decide), hp2.rest.gpr _ (by decide)]; exact h6)
    (by rw [u3.gpr]; rfl) (fun k hk => by have := out_lt (mask15 (VG.Proof.X25519.Arm.limb s.mem (State.addr b) X2)) (19 * (VG.Proof.X25519.Arm.limb s.mem (State.addr b) X2 15 / 32768)) k; unfold frA; omega) (by decide) ?_) fun s4 hp4 => ?_
  · intro k hk s' hp
    refine WP.mono (VG.Proof.X25519.Arm.ldSrc_ok (hc3.of_rest hp.rest (by decide)) (o := X2) (k := k) (by omega)) fun t ht => ⟨?_, ht.2.1.mono (by decide), ht.2.2⟩
    rw [ht.1, VG.Proof.X25519.Arm.wd_pass hc3 hp.frame (by omega) (by omega) (by omega), u3.mem]
    exact hpo2 k hk
  have hc4 : VG.Proof.X25519.Arm.Ctx b s4 := hc3.of_rest hp4.rest (by decide)
  have hpo4 : ∀ j < 16, wd s4.mem (State.addr b) (Y + 4 * j) = frY (VG.Proof.X25519.Arm.limb s.mem (State.addr b) X2) j :=
    fun j hj => by have := hp4.outs j hj; rwa [hc3.r0] at this
  have hpf4 : Frame [⟨State.addr b + BitVec.ofNat 64 Y, 64⟩] s3.mem s4.mem := by
    have := hp4.frame; rwa [hc3.r0] at this
  have hx4 : ∀ k < 16, VG.Proof.X25519.Arm.limb s4.mem (State.addr b) X2 k = frA (VG.Proof.X25519.Arm.limb s.mem (State.addr b) X2) k := by
    intro k hk
    rw [VG.Proof.X25519.Arm.limb, wd_frame hpf4 fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega),
      u3.mem, hpo2 k hk]
  refine WP.append (VG.Proof.X25519.Arm.freezeB_ok hc4) fun s5 ⟨h9, hy5, hf5, hr5⟩ => ?_
  have hc5 : VG.Proof.X25519.Arm.Ctx b s5 := hc4.of_rest hr5 (by decide)
  have hx5 : ∀ k < 16, VG.Proof.X25519.Arm.limb s5.mem (State.addr b) X2 k = frA (VG.Proof.X25519.Arm.limb s.mem (State.addr b) X2) k := by
    intro k hk
    rw [VG.Proof.X25519.Arm.limb, wd_frame hf5 fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)]
    exact hx4 k hk
  have hy5' : ∀ k < 16, VG.Proof.X25519.Arm.limb s5.mem (State.addr b) Y k = mask15 (frY (VG.Proof.X25519.Arm.limb s.mem (State.addr b) X2)) k := by
    intro k hk
    rw [hy5 k hk]
    simp only [mask15]
    split
    · rename_i h; subst h; rw [VG.Proof.X25519.Arm.limb, hpo4 15 (by decide)]
    · rw [VG.Proof.X25519.Arm.limb, hpo4 k hk]
  have h9' : s5.gpr .r9 = 0 - BitVec.ofNat 32 (frS (VG.Proof.X25519.Arm.limb s.mem (State.addr b) X2)) := by
    rw [h9, VG.Proof.X25519.Arm.limb, hpo4 15 (by decide)]; rfl
  have hr45 : Rest [.r1, .r2, .r3, .r4, .r5, .r6, .r9] s s5 :=
    (hr1.mono (by decide)).trans ((hp2.rest.mono (by decide)).trans ((u3.rest (by decide)).trans
      ((hp4.rest.mono (by decide)).trans (hr5.mono (by decide)))))
  refine WP.mono (VG.Proof.X25519.Arm.out_ok hc5 (o := o) (by rw [hr45.gpr _ (by decide), h12]) (by rw [hr45.wr]; exact hout) hofit
    hdisj hS h9') fun s6 h6' => ⟨?_, ?_, ?_⟩
  · have hr : ∀ k < 16, sel (frS (VG.Proof.X25519.Arm.limb s.mem (State.addr b) X2)) (VG.Proof.X25519.Arm.limb s5.mem (State.addr b) X2 k)
        (VG.Proof.X25519.Arm.limb s5.mem (State.addr b) Y k) = frR (VG.Proof.X25519.Arm.limb s.mem (State.addr b) X2) k := fun k hk => by
      rw [hx5 k hk, hy5' k hk]; rfl
    rw [VG.Proof.X25519.Arm.V, ← hv]
    exact VG.Proof.X25519.Arm.bytesAt_limbs hR (fun k hk => by rw [h6'.b0 k hk, hr k hk]) (fun k hk => by rw [h6'.b1 k hk, hr k hk])
  · exact (hr45.mono (by decide)).trans (h6'.rest.mono (by decide))
  · have hfa : ∀ z, z + 64 ≤ 1280 → 64 ≤ z → Region.Sub ⟨State.addr b + BitVec.ofNat 64 z, 64⟩ (VG.Proof.X25519.Arm.FA ACC b) :=
      fun z h1 h2 => Offset.sub _ (by omega) (by rw [VG.Proof.X25519.Arm.ACC_eq]; omega)
    refine (VG.Proof.X25519.Arm.frame_sub1 hf1 (hfa X2 (by omega) (by omega)) (List.mem_cons_self ..)).trans ?_
    refine (VG.Proof.X25519.Arm.frame_sub1 hpf2 (hfa X2 (by omega) (by omega)) (List.mem_cons_self ..)).trans ?_
    rw [← u3.mem]
    refine (VG.Proof.X25519.Arm.frame_sub1 hpf4 (hfa Y (by omega) (by omega)) (List.mem_cons_self ..)).trans ?_
    refine (VG.Proof.X25519.Arm.frame_sub1 hf5 (hfa Y (by omega) (by omega)) (List.mem_cons_self ..)).trans ?_
    exact VG.Proof.X25519.Arm.frame_sub1 h6'.frame (Region.sub_prefix (by omega)) (List.mem_cons_of_mem _ (List.mem_singleton_self _))

end

end VG.Proof.X25519.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.Arm.Setup`. -/
section

/-!
# X25519 on 32-bit ARM: the setup

The u-coordinate as 16-bit limbs (`decode_val`: the number of its 32 bytes
modulo `2²⁵⁵`), and the setup of the working space: the saved registers, `x1 =
x3 = u`, `x2 = z3 = 1`, `z2 = 0` and `a24` (`setup_ok`); the bits of the
scalar (`bits_ok`).
-/

namespace VG.Proof.X25519.Arm

open VG VG.Arm VG.Impl.X25519.Arm
open VG.Spec.X25519 (P Fe bytesAt a24)
open VG.Proof.X25519 (leNum leNum_append bytesAt_add bytesAt_succ length_bytesAt toFe)

/-! ## The u-coordinate as limbs -/

/-- Byte `i` at `p`, as a number. -/
def byteN (m : Mem) (p : Addr) (i : Nat) : Nat := (m (p + BitVec.ofNat 64 i)).toNat

/-- Limb `k` of the decoded u-coordinate: bytes `2k` and `2k + 1`, the top bit
masked. -/
def uLimb (m : Mem) (p : Addr) (k : Nat) : Nat :=
  VG.Proof.X25519.Arm.byteN m p (2 * k) + 256 * (if k = 15 then VG.Proof.X25519.Arm.byteN m p (2 * k + 1) % 128 else VG.Proof.X25519.Arm.byteN m p (2 * k + 1))

theorem leNum_bytesAt2 (m : Mem) (p : Addr) :
    ∀ n, leNum (bytesAt m p (2 * n)) = val16 (fun k => VG.Proof.X25519.Arm.byteN m p (2 * k) + 256 * VG.Proof.X25519.Arm.byteN m p (2 * k + 1)) n
  | 0 => rfl
  | n + 1 => by
    rw [show 2 * (n + 1) = 2 * n + 2 from rfl, bytesAt_add, leNum_append, VG.Proof.X25519.Arm.leNum_bytesAt2 m p n, val16_succ,
      length_bytesAt, show (256 : Nat) ^ (2 * n) = 2 ^ (16 * n) by
        rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]; congr 1; omega]
    congr 2
    rw [bytesAt_succ, bytesAt_succ, show bytesAt m (p + BitVec.ofNat 64 (2 * n) + 1 + 1) 0 = [] from rfl]
    simp only [leNum, VG.Proof.X25519.Arm.byteN, Nat.mul_zero, Nat.add_zero]
    rw [Offset.add_ofNat_add_one]

theorem uLimb_lt (m : Mem) (p : Addr) : ∀ k < 16, VG.Proof.X25519.Arm.uLimb m p k < 65536 := by
  intro k _
  have h0 := (m (p + BitVec.ofNat 64 (2 * k))).isLt
  have h1 := (m (p + BitVec.ofNat 64 (2 * k + 1))).isLt
  simp only [VG.Proof.X25519.Arm.uLimb, VG.Proof.X25519.Arm.byteN]
  split <;> omega

/-- The limbs of the decoded u-coordinate. -/
theorem decode_val (m : Mem) (p : Addr) :
    val16 (VG.Proof.X25519.Arm.uLimb m p) 16 = VG.Spec.X25519.decodeUCoordinate (bytesAt m p 32) := by
  rw [VG.Proof.X25519.decodeUCoordinate_eq (length_bytesAt m p 32), show 32 = 2 * 16 from rfl,
    VG.Proof.X25519.Arm.leNum_bytesAt2]
  have e : val16 (VG.Proof.X25519.Arm.uLimb m p) 15 = val16 (fun k => VG.Proof.X25519.Arm.byteN m p (2 * k) + 256 * VG.Proof.X25519.Arm.byteN m p (2 * k + 1)) 15 :=
    val16_congr fun k hk => by simp [VG.Proof.X25519.Arm.uLimb, show k ≠ 15 by omega]
  have hlo := val16_lt (f := VG.Proof.X25519.Arm.uLimb m p) (n := 15) fun k hk => VG.Proof.X25519.Arm.uLimb_lt m p k (by omega)
  rw [show 16 * 15 = 240 from rfl] at hlo
  rw [val16_succ (VG.Proof.X25519.Arm.uLimb m p) 15, val16_succ (fun k => VG.Proof.X25519.Arm.byteN m p (2 * k) + 256 * VG.Proof.X25519.Arm.byteN m p (2 * k + 1)) 15,
    ← e, show 16 * 15 = 240 from rfl]
  simp only [VG.Proof.X25519.Arm.uLimb, ite_true, show 2 * 15 = 30 from rfl, show 2 * 15 + 1 = 31 from rfl]
  have h31 := (m (p + BitVec.ofNat 64 31)).isLt
  have h30 := (m (p + BitVec.ofNat 64 30)).isLt
  simp only [VG.Proof.X25519.Arm.byteN] at *
  generalize (m (p + BitVec.ofNat 64 31)).toNat = x at *
  generalize (m (p + BitVec.ofNat 64 30)).toNat = y at *
  generalize val16 (VG.Proof.X25519.Arm.uLimb m p) 15 = L at *
  have hx : x = x % 128 + 128 * (x / 128) := (Nat.mod_add_div _ _).symm
  have hlt : L + 2 ^ 240 * (y + 256 * (x % 128)) < 2 ^ 255 := by
    have : 2 ^ 240 * (y + 256 * (x % 128)) ≤ 2 ^ 240 * 32767 :=
      Nat.mul_le_mul_left _ (by have := Nat.mod_lt x (show 128 > 0 by decide); omega)
    rw [show (2 : Nat) ^ 255 = 2 ^ 240 * 32768 from rfl]; omega
  rw [show L + 2 ^ 240 * (y + 256 * x) = L + 2 ^ 240 * (y + 256 * (x % 128)) + 2 ^ 255 * (x / 128) by
    conv => lhs; rw [hx]
    rw [show (2 : Nat) ^ 255 = 2 ^ 240 * 32768 from rfl]
    rw [Nat.mul_add 256, Nat.mul_add (2 ^ 240), Nat.mul_add (2 ^ 240), Nat.mul_assoc (2 ^ 240) 32768]
    omega, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

/-! ## Saving the registers -/

/-- The registers `g` saved at `[0, 32)` of the working space at `B`. -/
def Saved (B : Addr) (g : Reg → BitVec 32) (m : Mem) : Prop :=
  ∀ i < 8, m.readW (B + BitVec.ofNat 64 (4 * i)) 32 = g (savedReg i)

section
variable {b : BitVec 32}

theorem saves_ok {s : State} (h3 : s.gpr .r3 = b) (hfit : b.toNat + 4096 ≤ 2 ^ 32)
    (hw : (⟨State.addr b, 4096⟩ : Region) ∈ s.wr) :
    WP isa (.block ((List.range 8).flatMap fun i => [.str (savedReg i) .r3 (4 * i)])) s fun s' =>
      VG.Proof.X25519.Arm.Saved (State.addr b) s.gpr s'.mem ∧ Frame [⟨State.addr b, 32⟩] s.mem s'.mem ∧ s'.gpr = s.gpr ∧
        Rest [] s s' := by
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun n s' => (∀ i < n, s'.mem.readW (State.addr b + BitVec.ofNat 64 (4 * i)) 32 = s.gpr (savedReg i)) ∧
      Frame [⟨State.addr b, 4 * n⟩] s.mem s'.mem ∧ s'.gpr = s.gpr ∧ Rest [] s s')
    (fun n s' hn ⟨h1, h2, h3', h4⟩ => ?_) 8 (Nat.le_refl _) s
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), Frame.refl _ _, rfl, Rest.refl _ _⟩)
    fun s' h => ⟨h.1, h.2.1, h.2.2⟩
  refine wp_str (a := State.addr b + BitVec.ofNat 64 (4 * n)) (by omega)
    (by rw [h3', h3]; exact addr_add (by omega)) (by rw [h4.wr]; exact in_base hw (by omega) (by omega))
    fun s2 u2 => WP.block_nil ⟨fun i hi => ?_, ?_, by rw [u2.gpr, h3'], h4.trans (u2.rest _)⟩
  · rw [u2.mem]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]; exact h1 i hi
    · rw [Mem.readW_writeW_self32, h3']
  · rw [u2.mem]
    exact (h2.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega)⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))

/-! ## Decoding the u-coordinate -/

theorem toNat_setWidth8 (x : BitVec 8) : (x.setWidth 32).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans x.isLt (by decide))]

theorem decodeStep_ok {k : Nat} (hk : k < 16) {s : State} (hc : VG.Proof.X25519.Arm.Ctx b s) {pt : BitVec 32}
    (h2 : s.gpr .r2 = pt) (hpf : pt.toNat + 32 ≤ 2 ^ 32)
    (hin : (⟨State.addr pt, 32⟩ : Region) ∈ s.rd ++ s.wr) :
    WP isa (.block (decodeStep k)) s fun s' =>
      wd s'.mem (State.addr b) (X1 + 4 * k) = VG.Proof.X25519.Arm.uLimb s.mem (State.addr pt) k ∧
      wd s'.mem (State.addr b) (X3 + 4 * k) = VG.Proof.X25519.Arm.uLimb s.mem (State.addr pt) k ∧
      s'.mem = (s.mem.writeW (State.addr b + BitVec.ofNat 64 (X1 + 4 * k)) (BitVec.ofNat 32 (VG.Proof.X25519.Arm.uLimb s.mem (State.addr pt) k))).writeW
        (State.addr b + BitVec.ofNat 64 (X3 + 4 * k)) (BitVec.ofNat 32 (VG.Proof.X25519.Arm.uLimb s.mem (State.addr pt) k)) ∧
      Rest [.r4, .r5] s s' := by
  have hX1 : X1 = 64 := rfl
  have hX3 : X3 = 256 := rfl
  have hin' : ∀ i < 32, InRegions (s.rd ++ s.wr) (State.addr pt + BitVec.ofNat 64 i) 1 := fun i hi =>
    in_base hin (by omega) (by omega)
  have hlt := VG.Proof.X25519.Arm.uLimb_lt s.mem (State.addr pt) k hk
  have hb0 : VG.Proof.X25519.Arm.byteN s.mem (State.addr pt) (2 * k) < 256 := (s.mem (State.addr pt + BitVec.ofNat 64 (2 * k))).isLt
  have hb1 : VG.Proof.X25519.Arm.byteN s.mem (State.addr pt) (2 * k + 1) < 256 :=
    (s.mem (State.addr pt + BitVec.ofNat 64 (2 * k + 1))).isLt
  -- The two bytes, then (for limb 15) the mask, then the limb.
  have key : ∀ (is : List Instr) (s2 : State), Rest [.r4, .r5] s s2 → s2.mem = s.mem →
      (s2.gpr .r4).toNat = VG.Proof.X25519.Arm.byteN s.mem (State.addr pt) (2 * k) →
      (s2.gpr .r5).toNat = (if k = 15 then VG.Proof.X25519.Arm.byteN s.mem (State.addr pt) (2 * k + 1) % 128
        else VG.Proof.X25519.Arm.byteN s.mem (State.addr pt) (2 * k + 1)) →
      is = [.dp .add .r4 .r4 (.shifted .r5 .lsl 8), .str .r4 .r0 (X1 + 4 * k), .str .r4 .r0 (X3 + 4 * k)] →
      WP isa (.block is) s2 fun s' =>
        wd s'.mem (State.addr b) (X1 + 4 * k) = VG.Proof.X25519.Arm.uLimb s.mem (State.addr pt) k ∧
        wd s'.mem (State.addr b) (X3 + 4 * k) = VG.Proof.X25519.Arm.uLimb s.mem (State.addr pt) k ∧
        s'.mem = (s.mem.writeW (State.addr b + BitVec.ofNat 64 (X1 + 4 * k))
          (BitVec.ofNat 32 (VG.Proof.X25519.Arm.uLimb s.mem (State.addr pt) k))).writeW
          (State.addr b + BitVec.ofNat 64 (X3 + 4 * k)) (BitVec.ofNat 32 (VG.Proof.X25519.Arm.uLimb s.mem (State.addr pt) k)) ∧
        Rest [.r4, .r5] s s' := by
    intro is s2 hr2 hm2 e4 e5 his
    subst his
    have hc2 : VG.Proof.X25519.Arm.Ctx b s2 := hc.of_rest hr2 (by decide)
    refine wp_dp (op2_lsl (by decide)) fun s3 u3 => ?_
    have ev : s3.gpr .r4 = BitVec.ofNat 32 (VG.Proof.X25519.Arm.uLimb s.mem (State.addr pt) k) := by
      apply BitVec.eq_of_toNat_eq
      rw [u3.gpr]
      show (s2.gpr .r4 + s2.gpr .r5 <<< 8).toNat = _
      have h5 : (s2.gpr .r5).toNat < 256 := by rw [e5]; split <;> omega
      have h5' : (s2.gpr .r5).toNat * 2 ^ 8 % 2 ^ 32 = (s2.gpr .r5).toNat * 256 := Nat.mod_eq_of_lt (by omega)
      rw [toNat_add_lt (by rw [toNat_shl, h5', e4]; omega), toNat_shl, h5', e4, toNat_imm (by omega), VG.Proof.X25519.Arm.uLimb,
        ← e5]
      omega
    have hc3 : VG.Proof.X25519.Arm.Ctx b s3 := hc2.of_rest (u3.rest (ws := [.r4]) (by decide)) (by decide)
    refine VG.Proof.X25519.Arm.str0_ok hc3 (d := X1 + 4 * k) (by omega) fun s4 u4 => ?_
    refine VG.Proof.X25519.Arm.str0_ok (hc3.of_rest (u4.rest []) (by decide)) (d := X3 + 4 * k) (by omega) fun s5 u5 =>
      WP.block_nil ⟨?_, ?_, ?_, hr2.trans ((u3.rest (by decide)).trans ((u4.rest _).trans (u5.rest _)))⟩
    · rw [u5.mem, wd_write_other _ _ _ (by omega) (by omega) (by omega), u4.mem, wd_write_self, ev,
        toNat_imm (by omega)]
    · rw [u5.mem, wd_write_self, u4.gpr, ev, toNat_imm (by omega)]
    · rw [u5.mem, u4.gpr, u4.mem, u3.mem, hm2, ev]
  have e0 : State.addr (s.gpr .r2 + BitVec.ofNat 32 (2 * k)) = State.addr pt + BitVec.ofNat 64 (2 * k) := by
    rw [h2]; exact addr_add (by omega)
  have e1 : State.addr (s.gpr .r2 + BitVec.ofNat 32 (2 * k + 1)) =
      State.addr pt + BitVec.ofNat 64 (2 * k + 1) := by
    rw [h2]; exact addr_add (by omega)
  unfold decodeStep
  refine wp_ldrb (a := State.addr pt + BitVec.ofNat 64 (2 * k)) (by omega) e0 (hin' _ (by omega))
    fun s1 u1 => ?_
  refine wp_ldrb (a := State.addr pt + BitVec.ofNat 64 (2 * k + 1)) (by omega)
    (by rw [u1.other .r2 (by decide)]; exact e1) (by rw [u1.rd, u1.wr]; exact hin' _ (by omega)) fun s2 u2 => ?_
  have e4 : (s2.gpr .r4).toNat = VG.Proof.X25519.Arm.byteN s.mem (State.addr pt) (2 * k) := by
    rw [u2.other _ (by decide), u1.gpr, VG.Proof.X25519.Arm.toNat_setWidth8]; rfl
  have e5 : (s2.gpr .r5).toNat = VG.Proof.X25519.Arm.byteN s.mem (State.addr pt) (2 * k + 1) := by
    rw [u2.gpr, u1.mem, VG.Proof.X25519.Arm.toNat_setWidth8]; rfl
  have hr2 : Rest [.r4, .r5] s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  have hm2 : s2.mem = s.mem := by rw [u2.mem, u1.mem]
  by_cases h15 : k = 15
  · simp only [h15, ite_true]
    refine wp_dp (op2_imm (by decide)) fun s3 u3 => ?_
    subst h15
    refine key _ s3 (hr2.trans (u3.rest (by decide))) (by rw [u3.mem, hm2])
      (by rw [u3.other _ (by decide), e4]) ?_ rfl
    rw [u3.gpr]
    show (s2.gpr .r5 &&& 127).toNat = _
    rw [BitVec.toNat_and, e5, show (127 : BitVec 32).toNat = 2 ^ 7 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    rfl
  · simp only [h15, ite_false]
    exact key _ s2 hr2 hm2 e4 (by rw [e5, VG.Proof.X25519.Arm.iteF h15]) rfl

/-- A word outside a range that code wrote. -/
theorem wd_keep {m m' : Mem} {B : Addr} {o n d : Nat} (hf : Frame [⟨B + BitVec.ofNat 64 o, n⟩] m m')
    (hd : d + 4 ≤ o ∨ o + n ≤ d) (hb : d + 4 ≤ 4096) (ho : o + n ≤ 4096) : wd m' B d = wd m B d :=
  wd_frame hf fun r hr => by rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ hd (by omega) (by omega)

theorem decode_ok {s0 : State} (hc : VG.Proof.X25519.Arm.Ctx b s0) {pt : BitVec 32} (h2 : s0.gpr .r2 = pt)
    (hpf : pt.toNat + 32 ≤ 2 ^ 32) (hin : (⟨State.addr pt, 32⟩ : Region) ∈ s0.rd ++ s0.wr)
    (hd : Region.Disjoint ⟨State.addr pt, 32⟩ ⟨State.addr b, 4096⟩) :
    WP isa (.block ((List.range 16).flatMap decodeStep)) s0 fun s' =>
      (∀ k < 16, VG.Proof.X25519.Arm.limb s'.mem (State.addr b) X1 k = VG.Proof.X25519.Arm.uLimb s0.mem (State.addr pt) k ∧
        VG.Proof.X25519.Arm.limb s'.mem (State.addr b) X3 k = VG.Proof.X25519.Arm.uLimb s0.mem (State.addr pt) k) ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 X1, 256⟩] s0.mem s'.mem ∧ Rest [.r4, .r5] s0 s' := by
  have hX1 : X1 = 64 := rfl
  have hX3 : X3 = 256 := rfl
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun n s => (∀ k < n, VG.Proof.X25519.Arm.limb s.mem (State.addr b) X1 k = VG.Proof.X25519.Arm.uLimb s0.mem (State.addr pt) k ∧
        VG.Proof.X25519.Arm.limb s.mem (State.addr b) X3 k = VG.Proof.X25519.Arm.uLimb s0.mem (State.addr pt) k) ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 X1, 256⟩] s0.mem s.mem ∧ Rest [.r4, .r5] s0 s)
    (fun k s hk ⟨h1, hf, hr⟩ => ?_) 16 (Nat.le_refl _) s0
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), Frame.refl _ _, Rest.refl _ _⟩) fun s' h => h
  have hcs : VG.Proof.X25519.Arm.Ctx b s := hc.of_rest hr (by decide)
  refine WP.mono (VG.Proof.X25519.Arm.decodeStep_ok hk hcs (pt := pt) (by rw [hr.gpr _ (by decide), h2]) hpf
    (by rw [hr.rd, hr.wr]; exact hin)) fun s' ⟨e1, e3, hm, hr'⟩ => ⟨fun j hj => ?_, ?_, hr.trans hr'⟩
  · -- The bytes of the u-coordinate are as in `s0`.
    have hu : VG.Proof.X25519.Arm.uLimb s.mem (State.addr pt) k = VG.Proof.X25519.Arm.uLimb s0.mem (State.addr pt) k := by
      have hby : ∀ i < 32, s.mem (State.addr pt + BitVec.ofNat 64 i) = s0.mem (State.addr pt + BitVec.ofNat 64 i) :=
        fun i hi => hf _ fun r hr' => by
          rw [List.mem_singleton.mp hr'] at *
          intro hcon
          exact hd _ (Offset.contains_base _ (by omega) (by omega))
            ((Offset.sub_base (State.addr b) (d := X1) (n := 256) (k := 4096) (by omega)) _ hcon)
      simp only [VG.Proof.X25519.Arm.uLimb, VG.Proof.X25519.Arm.byteN, hby (2 * k) (by omega), hby (2 * k + 1) (by omega)]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [VG.Proof.X25519.Arm.limb, VG.Proof.X25519.Arm.limb, hm, wd_write_other _ _ _ (by omega) (by omega) (by omega),
        wd_write_other _ _ _ (by omega) (by omega) (by omega), wd_write_other _ _ _ (by omega) (by omega) (by omega),
        wd_write_other _ _ _ (by omega) (by omega) (by omega)]
      exact h1 j hj
    · rw [VG.Proof.X25519.Arm.limb, VG.Proof.X25519.Arm.limb, e1, e3, hu]; exact ⟨rfl, rfl⟩
  · rw [hm]
    exact (hf.writeW (List.mem_singleton_self _) _ (Offset.contains _ (by omega) (by omega) (by omega))).writeW
      (List.mem_singleton_self _) _ (Offset.contains _ (by omega) (by omega) (by omega))

/-- The ranges `consts` writes. -/
abbrev constsR (b : BitVec 32) : List Region :=
  [⟨State.addr b + BitVec.ofNat 64 X2, 128⟩, ⟨State.addr b + BitVec.ofNat 64 Z3, 64⟩,
    ⟨State.addr b + BitVec.ofNat 64 A24, 64⟩]

theorem constsR_sub (e k o n : Nat) (he : (⟨State.addr b + BitVec.ofNat 64 e, k⟩ : Region) ∈ VG.Proof.X25519.Arm.constsR b)
    (h1 : e ≤ o) (h2 : o + n ≤ e + k) : ∃ r ∈ VG.Proof.X25519.Arm.constsR b, Region.Sub ⟨State.addr b + BitVec.ofNat 64 o, n⟩ r :=
  ⟨_, he, Offset.sub (State.addr b) h1 h2⟩

theorem consts_ok {s : State} (hc : VG.Proof.X25519.Arm.Ctx b s) :
    WP isa (.block consts) s fun s' =>
      (∀ k < 16, VG.Proof.X25519.Arm.limb s'.mem (State.addr b) X2 k = if k = 0 then 1 else 0) ∧
      (∀ k < 16, VG.Proof.X25519.Arm.limb s'.mem (State.addr b) Z2 k = 0) ∧
      (∀ k < 16, VG.Proof.X25519.Arm.limb s'.mem (State.addr b) Z3 k = if k = 0 then 1 else 0) ∧
      (∀ k < 16, VG.Proof.X25519.Arm.limb s'.mem (State.addr b) A24 k = if k = 0 then 56129 else if k = 1 then 1 else 0) ∧
      Frame (VG.Proof.X25519.Arm.constsR b) s.mem s'.mem ∧ Rest [.r4, .r5, .r6] s s' := by
  have hX2 : X2 = 128 := rfl
  have hZ2 : Z2 = 192 := rfl
  have hZ3 : Z3 = 320 := rfl
  have hA : A24 = 960 := rfl
  simp only [consts, List.append_assoc, List.cons_append, List.nil_append]
  refine wp_mov (op2_imm (by decide)) fun s1 u1 => wp_mov (op2_imm (by decide)) fun s2 u2 =>
    wp_movw fun s3 u3 => ?_
  have hr3 : Rest [.r4, .r5, .r6] s s3 :=
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans (u3.rest (by decide)))
  have hc3 : VG.Proof.X25519.Arm.Ctx b s3 := hc.of_rest hr3 (by decide)
  have g4 : s3.gpr .r4 = 1 := by rw [u3.other _ (by decide), u2.other _ (by decide), u1.gpr]
  have g5 : s3.gpr .r5 = 0 := by rw [u3.other _ (by decide), u2.gpr]
  have g6 : (s3.gpr .r6).toNat = 56129 := by rw [u3.gpr]; rfl
  refine VG.Proof.X25519.Arm.str0_ok hc3 (d := X2) (by omega) fun s4 u4 => ?_
  refine VG.Proof.X25519.Arm.str0_ok (hc3.of_rest (u4.rest []) (by decide)) (d := Z2) (by omega) fun s5 u5 => ?_
  refine VG.Proof.X25519.Arm.str0_ok (hc3.of_rest ((u4.rest []).trans (u5.rest [])) (by decide)) (d := Z3) (by omega)
    fun s6 u6 => ?_
  have hr6 : Rest [] s3 s6 := (u4.rest []).trans ((u5.rest []).trans (u6.rest []))
  refine VG.Proof.X25519.Arm.str0_ok (hc3.of_rest hr6 (by decide)) (d := A24) (by omega) fun s7 u7 => ?_
  refine VG.Proof.X25519.Arm.str0_ok (hc3.of_rest (hr6.trans (u7.rest [])) (by decide)) (d := A24 + 4) (by omega) fun s8 u8 => ?_
  have hr8 : Rest [] s3 s8 := hr6.trans ((u7.rest []).trans (u8.rest []))
  have hc8 : VG.Proof.X25519.Arm.Ctx b s8 := hc3.of_rest hr8 (by decide)
  have hg8 : ∀ r, s8.gpr r = s3.gpr r := fun r => hr8.gpr r (by simp)
  have hm8 : s8.mem = ((((s3.mem.writeW (State.addr b + BitVec.ofNat 64 X2) (s3.gpr .r4)).writeW
      (State.addr b + BitVec.ofNat 64 Z2) (s3.gpr .r5)).writeW (State.addr b + BitVec.ofNat 64 Z3) (s3.gpr .r4)).writeW
      (State.addr b + BitVec.ofNat 64 A24) (s3.gpr .r6)).writeW (State.addr b + BitVec.ofNat 64 (A24 + 4)) (s3.gpr .r4) := by
    rw [u8.mem, u7.gpr, u7.mem, u6.gpr, u6.mem, u5.gpr, u5.mem, u4.gpr, u4.mem]
  refine WP.append (VG.Proof.X25519.Arm.stores_ok (r := .r5) (o := X2 + 4) (n := 15) (by omega) hc8) fun s9 ⟨w9, f9, g9, r9⟩ => ?_
  have hc9 : VG.Proof.X25519.Arm.Ctx b s9 := hc8.of_rest r9 (by decide)
  refine WP.append (VG.Proof.X25519.Arm.stores_ok (r := .r5) (o := Z2 + 4) (n := 15) (by omega) hc9) fun s10 ⟨w10, f10, g10, r10⟩ => ?_
  have hc10 : VG.Proof.X25519.Arm.Ctx b s10 := hc9.of_rest r10 (by decide)
  refine WP.append (VG.Proof.X25519.Arm.stores_ok (r := .r5) (o := Z3 + 4) (n := 15) (by omega) hc10)
    fun s11 ⟨w11, f11, g11, r11⟩ => ?_
  have hc11 : VG.Proof.X25519.Arm.Ctx b s11 := hc10.of_rest r11 (by decide)
  refine WP.mono (VG.Proof.X25519.Arm.stores_ok (r := .r5) (o := A24 + 8) (n := 14) (by omega) hc11)
    fun s12 ⟨w12, f12, g12, r12⟩ => ?_
  have e5 : ∀ t : State, t.gpr = s8.gpr → (t.gpr .r5).toNat = 0 := fun t ht => by rw [ht, hg8, g5]; rfl
  -- Words written by the first stores, through the later ones.
  have k8 : ∀ d, d + 4 ≤ 4096 → (d + 4 ≤ X2 + 4 ∨ X2 + 64 ≤ d) → (d + 4 ≤ Z2 + 4 ∨ Z2 + 64 ≤ d) →
      (d + 4 ≤ Z3 + 4 ∨ Z3 + 64 ≤ d) → (d + 4 ≤ A24 + 8 ∨ A24 + 64 ≤ d) →
      wd s12.mem (State.addr b) d = wd s8.mem (State.addr b) d := fun d hd h1 h2 h3 h4 => by
    rw [VG.Proof.X25519.Arm.wd_keep f12 h4 hd (by omega), VG.Proof.X25519.Arm.wd_keep f11 h3 hd (by omega), VG.Proof.X25519.Arm.wd_keep f10 h2 hd (by omega),
      VG.Proof.X25519.Arm.wd_keep f9 h1 hd (by omega)]
  have g9' : s9.gpr = s8.gpr := g9
  have g10' : s10.gpr = s8.gpr := g10.trans g9
  have g11' : s11.gpr = s8.gpr := g11.trans g10'
  refine ⟨fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [VG.Proof.X25519.Arm.limb, Nat.mul_zero, Nat.add_zero, k8 _ (by omega) (by omega) (by omega) (by omega) (by omega), hm8,
        wd_write_other _ _ _ (by omega) (by omega) (by omega), wd_write_other _ _ _ (by omega) (by omega) (by omega),
        wd_write_other _ _ _ (by omega) (by omega) (by omega), wd_write_other _ _ _ (by omega) (by omega) (by omega),
        wd_write_self, g4]; rfl
    · rw [VG.Proof.X25519.Arm.limb, VG.Proof.X25519.Arm.wd_keep f12 (by omega) (by omega) (by omega), VG.Proof.X25519.Arm.wd_keep f11 (by omega) (by omega) (by omega),
        VG.Proof.X25519.Arm.wd_keep f10 (by omega) (by omega) (by omega), show X2 + 4 * k = X2 + 4 + 4 * (k - 1) by omega,
        w9 (k - 1) (by omega), e5 _ rfl]
      simp only [show k ≠ 0 by omega, ite_false]
  · rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [VG.Proof.X25519.Arm.limb, Nat.mul_zero, Nat.add_zero, k8 _ (by omega) (by omega) (by omega) (by omega) (by omega), hm8,
        wd_write_other _ _ _ (by omega) (by omega) (by omega), wd_write_other _ _ _ (by omega) (by omega) (by omega),
        wd_write_other _ _ _ (by omega) (by omega) (by omega), wd_write_self, g5]; rfl
    · rw [VG.Proof.X25519.Arm.limb, VG.Proof.X25519.Arm.wd_keep f12 (by omega) (by omega) (by omega), VG.Proof.X25519.Arm.wd_keep f11 (by omega) (by omega) (by omega),
        show Z2 + 4 * k = Z2 + 4 + 4 * (k - 1) by omega, w10 (k - 1) (by omega), e5 _ g9']
  · rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [VG.Proof.X25519.Arm.limb, Nat.mul_zero, Nat.add_zero, k8 _ (by omega) (by omega) (by omega) (by omega) (by omega), hm8,
        wd_write_other _ _ _ (by omega) (by omega) (by omega), wd_write_other _ _ _ (by omega) (by omega) (by omega),
        wd_write_self, g4]; rfl
    · rw [VG.Proof.X25519.Arm.limb, VG.Proof.X25519.Arm.wd_keep f12 (by omega) (by omega) (by omega), show Z3 + 4 * k = Z3 + 4 + 4 * (k - 1) by omega,
        w11 (k - 1) (by omega), e5 _ g10']
      simp only [show k ≠ 0 by omega, ite_false]
  · rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hk2 with hk1 | rfl
      · rw [show k = 0 by omega, VG.Proof.X25519.Arm.limb, Nat.mul_zero, Nat.add_zero,
          k8 _ (by omega) (by omega) (by omega) (by omega) (by omega), hm8,
          wd_write_other _ _ _ (by omega) (by omega) (by omega), wd_write_self, g6]; rfl
      · rw [VG.Proof.X25519.Arm.limb, k8 _ (by omega) (by omega) (by omega) (by omega) (by omega), hm8,
          show A24 + 4 * 1 = A24 + 4 from rfl, wd_write_self, g4]; rfl
    · rw [VG.Proof.X25519.Arm.limb, show A24 + 4 * k = A24 + 8 + 4 * (k - 2) by omega, w12 (k - 2) (by omega), e5 _ g11']
      simp only [show k ≠ 0 by omega, show k ≠ 1 by omega, ite_false]
  · -- Every write is in `constsR`.
    have m1 : (⟨State.addr b + BitVec.ofNat 64 X2, 128⟩ : Region) ∈ VG.Proof.X25519.Arm.constsR b := List.mem_cons_self ..
    have m2 : (⟨State.addr b + BitVec.ofNat 64 Z3, 64⟩ : Region) ∈ VG.Proof.X25519.Arm.constsR b :=
      List.mem_cons_of_mem _ (List.mem_cons_self ..)
    have m3 : (⟨State.addr b + BitVec.ofNat 64 A24, 64⟩ : Region) ∈ VG.Proof.X25519.Arm.constsR b :=
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    have f8 : Frame (VG.Proof.X25519.Arm.constsR b) s.mem s8.mem := by
      rw [hm8, u3.mem, u2.mem, u1.mem]
      exact (((((Frame.refl _ _).writeW m1 (s3.gpr .r4) (Offset.contains _ (d := X2) (n := 4) (by omega) (by omega)
        (by omega))).writeW m1 (s3.gpr .r5) (Offset.contains _ (d := Z2) (n := 4) (by omega) (by omega)
        (by omega))).writeW m2 (s3.gpr .r4) (Offset.contains _ (d := Z3) (n := 4) (by omega) (by omega)
        (by omega))).writeW m3 (s3.gpr .r6) (Offset.contains _ (d := A24) (n := 4) (by omega) (by omega)
        (by omega))).writeW m3 (s3.gpr .r4) (Offset.contains _ (d := A24 + 4) (n := 4) (by omega) (by omega)
        (by omega))
    exact f8.trans ((f9.sub fun r hr => by rw [List.mem_singleton.mp hr]; exact VG.Proof.X25519.Arm.constsR_sub _ _ _ _ m1 (by omega) (by omega)).trans
      ((f10.sub fun r hr => by rw [List.mem_singleton.mp hr]; exact VG.Proof.X25519.Arm.constsR_sub _ _ _ _ m1 (by omega) (by omega)).trans
      ((f11.sub fun r hr => by rw [List.mem_singleton.mp hr]; exact VG.Proof.X25519.Arm.constsR_sub _ _ _ _ m2 (by omega) (by omega)).trans
      (f12.sub fun r hr => by rw [List.mem_singleton.mp hr]; exact VG.Proof.X25519.Arm.constsR_sub _ _ _ _ m3 (by omega) (by omega)))))
  · exact hr3.trans ((hr8.mono (by decide)).trans ((r9.mono (by decide)).trans ((r10.mono (by decide)).trans
      ((r11.mono (by decide)).trans (r12.mono (by decide))))))

end

/-! ## The whole setup -/

/-- The precondition of `vg_x25519(out = r0, scalar = r1, point = r2, scratch = r3)`, by field. -/
structure XPre (s : State) : Prop where
  rd : s.rd = [⟨State.addr (s.gpr .r1), 32⟩, ⟨State.addr (s.gpr .r2), 32⟩]
  wr : s.wr = [⟨State.addr (s.gpr .r0), 32⟩, ⟨State.addr (s.gpr .r3), 4096⟩]
  out_sc : Region.Disjoint ⟨State.addr (s.gpr .r0), 32⟩ ⟨State.addr (s.gpr .r1), 32⟩
  out_pt : Region.Disjoint ⟨State.addr (s.gpr .r0), 32⟩ ⟨State.addr (s.gpr .r2), 32⟩
  out_ws : Region.Disjoint ⟨State.addr (s.gpr .r0), 32⟩ ⟨State.addr (s.gpr .r3), 4096⟩
  sc_ws : Region.Disjoint ⟨State.addr (s.gpr .r1), 32⟩ ⟨State.addr (s.gpr .r3), 4096⟩
  pt_ws : Region.Disjoint ⟨State.addr (s.gpr .r2), 32⟩ ⟨State.addr (s.gpr .r3), 4096⟩
  f0 : (s.gpr .r0).toNat + 32 ≤ 2 ^ 32
  f1 : (s.gpr .r1).toNat + 32 ≤ 2 ^ 32
  f2 : (s.gpr .r2).toNat + 32 ≤ 2 ^ 32
  f3 : (s.gpr .r3).toNat + 4096 ≤ 2 ^ 32

/-- The u-coordinate, decoded. -/
def uOf (s : State) : Fe :=
  toFe (VG.Spec.X25519.decodeUCoordinate (bytesAt s.mem (State.addr (s.gpr .r2)) 32))

theorem val16_one : val16 (fun k => if k = 0 then 1 else 0) 16 = 1 := by decide
theorem val16_zero16 : val16 (fun _ => 0) 16 = 0 := by decide
theorem val16_a24 : val16 (fun k => if k = 0 then 56129 else if k = 1 then 1 else 0) 16 = 121665 := by decide

theorem slot_of {m : Mem} {B : Addr} {o : Nat} {f : Nat → Nat} (h : ∀ k < 16, VG.Proof.X25519.Arm.limb m B o k = f k)
    (hf : ∀ k < 16, f k < 65536) : VG.Proof.X25519.Arm.Lim m B o ∧ VG.Proof.X25519.Arm.FS m B o = toFe (val16 f 16) :=
  ⟨fun k hk => by rw [h k hk]; exact hf k hk, by rw [VG.Proof.X25519.Arm.FS, VG.Proof.X25519.Arm.V, val16_congr h]⟩

theorem setup_ok {s : State} (hp : VG.Proof.X25519.Arm.XPre s) :
    WP isa (.block setup) s fun s' =>
      VG.Proof.X25519.Arm.Ctx (s.gpr .r3) s' ∧ s'.gpr .r12 = s.gpr .r0 ∧ s'.gpr .r1 = s.gpr .r1 ∧
      VG.Proof.X25519.Arm.Saved (State.addr (s.gpr .r3)) s.gpr s'.mem ∧
      Frame [⟨State.addr (s.gpr .r3), 4096⟩] s.mem s'.mem ∧
      VG.Proof.X25519.Arm.SlotsOk s'.mem (State.addr (s.gpr .r3)) VG.Proof.X25519.Arm.LQ (VG.Proof.X25519.Arm.ladV (VG.Proof.X25519.Arm.uOf s) (VG.Proof.X25519.init (VG.Proof.X25519.Arm.uOf s))) ∧
      Rest [.r0, .r4, .r5, .r6, .r12] s s' := by
  have hX1 : X1 = 64 := rfl
  have hX2 : X2 = 128 := rfl
  have hZ2 : Z2 = 192 := rfl
  have hX3 : X3 = 256 := rfl
  have hZ3 : Z3 = 320 := rfl
  have hA : A24 = 960 := rfl
  have hws : (⟨State.addr (s.gpr .r3), 4096⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  simp only [setup, List.append_assoc, List.cons_append, List.nil_append]
  refine WP.append (VG.Proof.X25519.Arm.saves_ok rfl hp.f3 hws) fun s1 ⟨hsv, hf1, hg1, hr1⟩ => ?_
  refine wp_mov (op2_reg _ _) fun s2 u2 => wp_mov (op2_reg _ _) fun s3 u3 => ?_
  have hr3 : Rest [.r0, .r12] s s3 := (hr1.mono (by decide)).trans ((u2.rest (by decide)).trans (u3.rest (by decide)))
  have hc3 : VG.Proof.X25519.Arm.Ctx (s.gpr .r3) s3 :=
    ⟨by rw [u3.gpr, u2.other _ (by decide), hg1], hp.f3, by rw [hr3.wr]; exact hws⟩
  have hm3 : s3.mem = s1.mem := by rw [u3.mem, u2.mem]
  refine WP.append (VG.Proof.X25519.Arm.decode_ok hc3 (pt := s.gpr .r2) (by rw [hr3.gpr _ (by decide)]) hp.f2
    (by rw [hr3.rd, hp.rd]; simp) hp.pt_ws) fun s4 ⟨hl4, hf4, hr4⟩ => ?_
  have hc4 : VG.Proof.X25519.Arm.Ctx (s.gpr .r3) s4 := hc3.of_rest hr4 (by decide)
  refine WP.mono (VG.Proof.X25519.Arm.consts_ok hc4) fun s5 ⟨hx2, hz2, hz3, ha24, hf5, hr5⟩ => ?_
  -- The u-coordinate's bytes did not change.
  have hu : ∀ k < 16, VG.Proof.X25519.Arm.uLimb s3.mem (State.addr (s.gpr .r2)) k = VG.Proof.X25519.Arm.uLimb s.mem (State.addr (s.gpr .r2)) k := by
    intro k hk
    have hby : ∀ i < 32, s3.mem (State.addr (s.gpr .r2) + BitVec.ofNat 64 i) =
        s.mem (State.addr (s.gpr .r2) + BitVec.ofNat 64 i) := fun i hi => by
      rw [hm3]
      refine hf1 _ fun r hr hcon => ?_
      rw [List.mem_singleton.mp hr] at hcon
      exact hp.pt_ws _ (Offset.contains_base _ (by omega) (by omega))
        ((Region.sub_prefix (base := State.addr (s.gpr .r3)) (len := 32) (len' := 4096) (by omega)) _ hcon)
    simp only [VG.Proof.X25519.Arm.uLimb, VG.Proof.X25519.Arm.byteN, hby (2 * k) (by omega), hby (2 * k + 1) (by omega)]
  -- `x1` and `x3` through the constants.
  have hkeep : ∀ o, (o = X1 ∨ o = X3) → ∀ k < 16,
      VG.Proof.X25519.Arm.limb s5.mem (State.addr (s.gpr .r3)) o k = VG.Proof.X25519.Arm.uLimb s.mem (State.addr (s.gpr .r2)) k := by
    intro o ho k hk
    have e := VG.Proof.X25519.Arm.limb_frame (o := o) hf5 fun r hr j hj => by
      simp only [VG.Proof.X25519.Arm.constsR, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact Offset.disjoint _ (by omega) (by omega) (by omega)
    rw [e k hk, ← hu k hk]
    rcases ho with rfl | rfl
    · exact (hl4 k hk).1
    · exact (hl4 k hk).2
  refine ⟨hc4.of_rest hr5 (by decide), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hr5.gpr _ (by decide), hr4.gpr _ (by decide), u3.other _ (by decide), u2.gpr, hg1]
  · rw [hr5.gpr _ (by decide), hr4.gpr _ (by decide), u3.other _ (by decide), u2.other _ (by decide), hg1]
  · intro i hi
    rw [← hsv i hi, ← hm3]
    have hd : ∀ (rs : List Region), (∀ r ∈ rs, ∃ o n, r = ⟨State.addr (s.gpr .r3) + BitVec.ofNat 64 o, n⟩ ∧
        32 ≤ o ∧ o + n ≤ 4096) → ∀ r ∈ rs,
        (⟨State.addr (s.gpr .r3) + BitVec.ofNat 64 (4 * i), 4⟩ : Region).Disjoint r := fun rs h r hr => by
      obtain ⟨o, n, rfl, h1, h2⟩ := h r hr
      exact Offset.disjoint _ (by omega) (by omega) (by omega)
    rw [hf5.readW (Region.contains_self _ _) (hd _ fun r hr => by
        simp only [VG.Proof.X25519.Arm.constsR, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨X2, 128, rfl, by omega, by omega⟩
        · exact ⟨Z3, 64, rfl, by omega, by omega⟩
        · exact ⟨A24, 64, rfl, by omega, by omega⟩) (by decide),
      hf4.readW (Region.contains_self _ _) (hd _ fun r hr => by
        rw [List.mem_singleton.mp hr]; exact ⟨X1, 256, rfl, by omega, by omega⟩) (by decide)]
  · have hsub : ∀ o n, o + n ≤ 4096 → Region.Sub ⟨State.addr (s.gpr .r3) + BitVec.ofNat 64 o, n⟩
        ⟨State.addr (s.gpr .r3), 4096⟩ := fun o n h => Offset.sub_base _ h
    refine (hf1.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega)⟩).trans ?_
    rw [← hm3]
    refine (hf4.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact hsub _ _ (by omega)⟩).trans ?_
    refine hf5.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩
    simp only [VG.Proof.X25519.Arm.constsR, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hsub _ _ (by omega)
  · intro q hq
    simp only [VG.Proof.X25519.Arm.LQ, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨h1, h2⟩ := VG.Proof.X25519.Arm.slot_of (hkeep _ (.inl rfl)) (VG.Proof.X25519.Arm.uLimb_lt _ _)
      refine ⟨h1, ?_⟩
      rw [h2, VG.Proof.X25519.Arm.decode_val]; simp only [VG.Proof.X25519.Arm.ladV, ite_true]; rfl
    · obtain ⟨h1, h2⟩ := VG.Proof.X25519.Arm.slot_of hx2 (fun k _ => by split <;> decide)
      refine ⟨h1, ?_⟩
      rw [h2, VG.Proof.X25519.Arm.val16_one]; simp only [VG.Proof.X25519.Arm.ladV, VG.Proof.X25519.init, VG.Proof.X25519.Arm.iteF (show X2 ≠ X1 by decide), ite_true]; rfl
    · obtain ⟨h1, h2⟩ := VG.Proof.X25519.Arm.slot_of hz2 (fun k _ => by decide)
      refine ⟨h1, ?_⟩
      rw [h2, VG.Proof.X25519.Arm.val16_zero16]
      simp only [VG.Proof.X25519.Arm.ladV, VG.Proof.X25519.init, VG.Proof.X25519.Arm.iteF (show Z2 ≠ X1 by decide), VG.Proof.X25519.Arm.iteF (show Z2 ≠ X2 by decide),
        ite_true]; rfl
    · obtain ⟨h1, h2⟩ := VG.Proof.X25519.Arm.slot_of (hkeep _ (.inr rfl)) (VG.Proof.X25519.Arm.uLimb_lt _ _)
      refine ⟨h1, ?_⟩
      rw [h2, VG.Proof.X25519.Arm.decode_val]
      simp only [VG.Proof.X25519.Arm.ladV, VG.Proof.X25519.init, VG.Proof.X25519.Arm.iteF (show X3 ≠ X1 by decide), VG.Proof.X25519.Arm.iteF (show X3 ≠ X2 by decide),
        VG.Proof.X25519.Arm.iteF (show X3 ≠ Z2 by decide), ite_true]; rfl
    · obtain ⟨h1, h2⟩ := VG.Proof.X25519.Arm.slot_of hz3 (fun k _ => by split <;> decide)
      refine ⟨h1, ?_⟩
      rw [h2, VG.Proof.X25519.Arm.val16_one]
      simp only [VG.Proof.X25519.Arm.ladV, VG.Proof.X25519.init, VG.Proof.X25519.Arm.iteF (show Z3 ≠ X1 by decide), VG.Proof.X25519.Arm.iteF (show Z3 ≠ X2 by decide),
        VG.Proof.X25519.Arm.iteF (show Z3 ≠ Z2 by decide), VG.Proof.X25519.Arm.iteF (show Z3 ≠ X3 by decide), ite_true]; rfl
    · obtain ⟨h1, h2⟩ := VG.Proof.X25519.Arm.slot_of ha24 (fun k _ => by split <;> [decide; split <;> decide])
      refine ⟨h1, ?_⟩
      rw [h2, VG.Proof.X25519.Arm.val16_a24]
      simp only [VG.Proof.X25519.Arm.ladV, VG.Proof.X25519.Arm.iteF (show A24 ≠ X1 by decide), VG.Proof.X25519.Arm.iteF (show A24 ≠ X2 by decide),
        VG.Proof.X25519.Arm.iteF (show A24 ≠ Z2 by decide), VG.Proof.X25519.Arm.iteF (show A24 ≠ X3 by decide), VG.Proof.X25519.Arm.iteF (show A24 ≠ Z3 by decide)]; rfl
  · exact (hr3.mono (by decide)).trans ((hr4.mono (by decide)).trans (hr5.mono (by decide)))

end VG.Proof.X25519.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.Arm.Bits`. -/
section

/-!
# X25519 on 32-bit ARM: the bits of the scalar

`bits` stores bit `t` of the decoded (clamped) scalar at byte `BITS + t` of
the working space, for `t < 255` (`bits_ok`).
-/

namespace VG.Proof.X25519.Arm

open VG VG.Arm VG.Impl.X25519.Arm
open VG.Spec.X25519 (P Fe bytesAt)
open VG.Proof.X25519 (bit)

/-- Bit `t` of the scalar's bytes at `SC`, unclamped. -/
def rawBit (m : Mem) (SC : Addr) (t : Nat) : Nat := ((m (SC + BitVec.ofNat 64 (t / 8))).toNat >>> (t % 8)) &&& 1

theorem rawBit_le (m : Mem) (SC : Addr) (t : Nat) : VG.Proof.X25519.Arm.rawBit m SC t ≤ 1 := by
  simp only [VG.Proof.X25519.Arm.rawBit]; exact Nat.le_of_lt_succ (Nat.and_lt_two_pow _ (by decide : 1 < 2 ^ 1))

theorem getD_bytesAt (m : Mem) (p : Addr) {n i : Nat} (hi : i < n) :
    (bytesAt m p n).getD i 0 = m (p + BitVec.ofNat 64 i) := by
  simp [bytesAt, List.getD_eq_getElem?_getD, hi]

theorem strb_byte {v : BitVec 32} {x : Nat} (h : v.toNat = x) :
    v.setWidth 8 = BitVec.ofNat 8 x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, h, BitVec.toNat_ofNat]

section
variable {b : BitVec 32}

/-- While storing the bits of byte `i`, from `s1` (with the byte in `r4`),
after `j` bits. -/
structure JInv (b : BitVec 32) (i : Nat) (x : Nat) (s1 : State) (j : Nat) (s : State) : Prop where
  rest : Rest [.r5] s1 s
  frame : Frame [⟨State.addr b + BitVec.ofNat 64 (BITS + 8 * i), j⟩] s1.mem s.mem
  bits : ∀ j' < j, s.mem (State.addr b + BitVec.ofNat 64 (BITS + 8 * i + j')) = BitVec.ofNat 8 ((x >>> j') &&& 1)

theorem bitStep_ok {i j : Nat} (hi : i < 32) (hj : j < 8) {x : Nat} {s1 s : State}
    (hc : VG.Proof.X25519.Arm.Ctx b s1) (h4 : (s1.gpr .r4).toNat = x) (h6 : s1.gpr .r6 = b + BitVec.ofNat 32 (8 * i))
    (h : VG.Proof.X25519.Arm.JInv b i x s1 j s) :
    WP isa (.block ((if j = 0 then ([.dp .and .r5 .r4 (.imm 1)] : List Instr)
      else ([.mov .r5 (.shifted .r4 .lsr j), .dp .and .r5 .r5 (.imm 1)] : List Instr)) ++
      ([.strb .r5 .r6 (BITS + j)] : List Instr))) s
      (VG.Proof.X25519.Arm.JInv b i x s1 (j + 1)) := by
  have hB : BITS = 1280 := rfl
  have hfit := hc.fit
  have e4 : (s.gpr .r4).toNat = x := by rw [h.rest.gpr _ (by decide), h4]
  -- The bit, into `r5`.
  have key : ∀ s2 : State, Rest [.r5] s s2 → s2.mem = s.mem → (s2.gpr .r5).toNat = (x >>> j) &&& 1 →
      WP isa (.block [.strb .r5 .r6 (BITS + j)]) s2 (VG.Proof.X25519.Arm.JInv b i x s1 (j + 1)) := by
    intro s2 hr2 hm2 e5
    have e6 : s2.gpr .r6 = b + BitVec.ofNat 32 (8 * i) := by
      rw [hr2.gpr _ (by decide), h.rest.gpr _ (by decide), h6]
    refine wp_strb (a := State.addr b + BitVec.ofNat 64 (BITS + 8 * i + j)) (by omega)
      (by rw [e6, VG.Proof.X25519.Arm.ea2 hfit (by omega)]; congr 2; omega)
      (by rw [hr2.wr, h.rest.wr]; exact hc.inW (by omega)) fun s3 u3 => WP.block_nil ⟨?_, ?_, fun j' hj' => ?_⟩
    · exact h.rest.trans (hr2.trans (u3.rest _))
    · rw [u3.mem, hm2]
      exact (h.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega)⟩).writeW
        (List.mem_singleton_self _) _ (Offset.contains _ (by omega) (by omega) (by omega))
    · rw [u3.mem, VG.WriteBytes.writeW8_apply, hm2]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj' with hj' | rfl
      · rw [VG.Proof.X25519.Arm.iteF (Offset.add_ofNat_ne _ (by omega) (by omega) (by omega))]; exact h.bits j' hj'
      · rw [VG.Proof.X25519.Arm.iteT rfl]; exact VG.Proof.X25519.Arm.strb_byte e5
  by_cases h0 : j = 0
  · subst h0
    simp only [ite_true, List.cons_append, List.nil_append]
    refine wp_dp (op2_imm (by decide)) fun s2 u2 => key s2 (u2.rest (by decide)) u2.mem ?_
    rw [u2.gpr]
    show (s.gpr .r4 &&& 1).toNat = _
    rw [BitVec.toNat_and, e4, Nat.shiftRight_zero]; rfl
  · simp only [h0, ite_false, List.cons_append, List.nil_append]
    refine wp_mov (op2_lsr (by omega)) fun s2 u2 => wp_dp (op2_imm (by decide)) fun s3 u3 =>
      key s3 ((u2.rest (by decide)).trans (u3.rest (by decide))) (by rw [u3.mem, u2.mem]) ?_
    rw [u3.gpr]
    show (s2.gpr .r5 &&& 1).toNat = _
    rw [BitVec.toNat_and, u2.gpr, toNat_shr, e4, Nat.shiftRight_eq_div_pow]; rfl

/-- The loop invariant of `bits` from `s0`, before byte `i`. -/
structure BInv (b : BitVec 32) (sc : BitVec 32) (s0 : State) (i : Nat) (s : State) : Prop where
  ctx : VG.Proof.X25519.Arm.Ctx b s
  rest : Rest [.r1, .r4, .r5, .r6, .r7] s0 s
  r1 : s.gpr .r1 = sc + BitVec.ofNat 32 i
  r6 : s.gpr .r6 = b + BitVec.ofNat 32 (8 * i)
  r7 : s.gpr .r7 = BitVec.ofNat 32 (32 - i)
  frame : Frame [⟨State.addr b + BitVec.ofNat 64 BITS, 8 * i⟩] s0.mem s.mem
  bits : ∀ t < 8 * i, s.mem (State.addr b + BitVec.ofNat 64 (BITS + t)) = BitVec.ofNat 8 (VG.Proof.X25519.Arm.rawBit s0.mem (State.addr sc) t)

theorem bitsBody_ok {sc : BitVec 32} {s0 : State} (hsc : sc.toNat + 32 ≤ 2 ^ 32)
    (hin : (⟨State.addr sc, 32⟩ : Region) ∈ s0.rd ++ s0.wr)
    (hd : Region.Disjoint ⟨State.addr sc, 32⟩ ⟨State.addr b, 4096⟩) {i : Nat} (hi : i < 32) {s : State}
    (h : VG.Proof.X25519.Arm.BInv b sc s0 i s) :
    WP isa (.block bitsBody) s fun s' => VG.Proof.X25519.Arm.BInv b sc s0 (i + 1) s' ∧ s'.z = decide (32 - (i + 1) = 0) := by
  have hB : BITS = 1280 := rfl
  have hfit := h.ctx.fit
  unfold bitsBody
  simp only [List.cons_append, List.nil_append]
  refine wp_ldrb (a := State.addr sc + BitVec.ofNat 64 i) (by decide)
    (by rw [h.r1, BitVec.add_zero]; exact addr_add (by omega))
    (by rw [h.rest.rd, h.rest.wr]; exact in_base hin (by omega) (by omega)) fun s1 u1 => ?_
  have hc1 : VG.Proof.X25519.Arm.Ctx b s1 := h.ctx.of_rest (u1.rest (ws := [.r4]) (by decide)) (by decide)
  -- The byte, as in `s0`.
  have hx : (s1.gpr .r4).toNat = (s0.mem (State.addr sc + BitVec.ofNat 64 i)).toNat := by
    rw [u1.gpr, VG.Proof.X25519.Arm.toNat_setWidth8]
    congr 1
    refine h.frame _ fun r hr hcon => ?_
    rw [List.mem_singleton.mp hr] at hcon
    exact hd _ (Offset.contains_base _ (by omega) (by omega))
      ((Offset.sub_base (State.addr b) (d := BITS) (n := 8 * i) (k := 4096) (by omega)) _ hcon)
  refine WP.append (wp_range_flatMap (M := isa) (VG.Proof.X25519.Arm.JInv b i (s0.mem (State.addr sc + BitVec.ofNat 64 i)).toNat s1)
    (fun j s' hj h' => VG.Proof.X25519.Arm.bitStep_ok hi hj hc1 hx (by rw [u1.other _ (by decide), h.r6]) h') 8 (Nat.le_refl _) s1
    ⟨Rest.refl _ _, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun s2 h2 => ?_
  refine wp_dp (op2_imm (by decide)) fun s3 u3 => wp_dp (op2_imm (by decide)) fun s4 u4 =>
    wp_subs (op2_imm (by decide)) fun s5 u5 hz => WP.block_nil ?_
  have hr5 : Rest [.r1, .r4, .r5, .r6, .r7] s s5 :=
    (u1.rest (by decide)).trans ((h2.rest.mono (by decide)).trans ((u3.rest (by decide)).trans
      ((u4.rest (by decide)).trans (u5.rest (by decide)))))
  have hm5 : s5.mem = s2.mem := by rw [u5.mem, u4.mem, u3.mem]
  have r7' : s5.gpr .r7 = BitVec.ofNat 32 (32 - (i + 1)) := by
    rw [u5.gpr, u4.other _ (by decide), u3.other _ (by decide), h2.rest.gpr _ (by decide),
      u1.other _ (by decide), h.r7]
    have t1 : (1 : BitVec 32).toNat = 1 := rfl
    apply BitVec.eq_of_toNat_eq
    rw [toNat_sub_le (by rw [toNat_imm (by omega), t1]; omega), toNat_imm (by omega), toNat_imm (by omega), t1]
    omega
  refine ⟨⟨h.ctx.of_rest hr5 (by decide), h.rest.trans hr5, ?_, ?_, r7', ?_, fun t ht => ?_⟩, ?_⟩
  · rw [u5.other _ (by decide), u4.other _ (by decide), u3.gpr]
    show s2.gpr .r1 + BitVec.ofNat 32 1 = _
    rw [h2.rest.gpr _ (by decide), u1.other _ (by decide), h.r1, Offset.add_add]
  · rw [u5.other _ (by decide), u4.gpr]
    show s3.gpr .r6 + BitVec.ofNat 32 8 = _
    rw [u3.other _ (by decide), h2.rest.gpr _ (by decide), u1.other _ (by decide), h.r6, Offset.add_add,
      Nat.mul_succ]
  · rw [hm5]
    refine (h.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega)⟩).trans ?_
    rw [← u1.mem]
    exact h2.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by omega) (by omega)⟩
  · rw [hm5]
    rcases Nat.lt_or_ge t (8 * i) with ht' | ht'
    · rw [h2.frame _ fun r hr hcon => by
        rw [List.mem_singleton.mp hr] at hcon
        exact Offset.disjoint (State.addr b) (d := BITS + t) (n := 1) (e := BITS + 8 * i) (k := 8)
          (.inl (by omega)) (by omega) (by omega) _ (Region.contains_self _ _) hcon, u1.mem]
      exact h.bits t ht'
    · have := h2.bits (t - 8 * i) (by omega)
      rw [show BITS + 8 * i + (t - 8 * i) = BITS + t by omega] at this
      rw [this]
      simp only [VG.Proof.X25519.Arm.rawBit, show t / 8 = i by omega, show t % 8 = t - 8 * i by omega]
  · rw [hz, ← u5.gpr, r7', ofNat_beq_zero (by omega)]

theorem bits_ok {sc : BitVec 32} {s : State} (hc : VG.Proof.X25519.Arm.Ctx b s) (h1 : s.gpr .r1 = sc)
    (hsc : sc.toNat + 32 ≤ 2 ^ 32) (hin : (⟨State.addr sc, 32⟩ : Region) ∈ s.rd ++ s.wr)
    (hd : Region.Disjoint ⟨State.addr sc, 32⟩ ⟨State.addr b, 4096⟩) :
    WP isa VG.Impl.X25519.Arm.bits s fun s' => VG.Proof.X25519.Arm.Ctx b s' ∧ Rest [.r1, .r4, .r5, .r6, .r7] s s' ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 BITS, 256⟩] s.mem s'.mem ∧
      VG.Proof.X25519.Arm.Bits b (VG.Spec.X25519.decodeScalar25519 (bytesAt s.mem (State.addr sc) 32)) s'.mem := by
  have hB : BITS = 1280 := rfl
  have hfit := hc.fit
  unfold VG.Impl.X25519.Arm.bits
  refine WP.seq (wp_mov (op2_reg _ _) fun s1 u1 => wp_mov (op2_imm (by decide)) fun s2 u2 => WP.block_nil ?_)
  have hr2 : Rest [.r6, .r7] s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  have hm2 : s2.mem = s.mem := by rw [u2.mem, u1.mem]
  have h0 : VG.Proof.X25519.Arm.BInv b sc s2 0 s2 :=
    ⟨hc.of_rest hr2 (by decide), Rest.refl _ _, by rw [hr2.gpr _ (by decide), h1]; exact (BitVec.add_zero _).symm,
      by rw [u2.other _ (by decide), u1.gpr, hc.r0]; exact (BitVec.add_zero _).symm, by rw [u2.gpr]; rfl,
      Frame.refl _ _, fun t ht => absurd ht (by omega)⟩
  refine WP.seq (WP.mono (Q := VG.Proof.X25519.Arm.BInv b sc s2 32) (WP.loop (M := isa)
    (fun m s' => ∃ i, m = 32 - i ∧ i < 32 ∧ VG.Proof.X25519.Arm.BInv b sc s2 i s') ?_ 32 s2 ⟨0, rfl, by decide, h0⟩)
    fun s3 h3 => ?_)
  · rintro m s' ⟨i, rfl, hi, hb⟩
    refine WP.mono (VG.Proof.X25519.Arm.bitsBody_ok hsc (by rw [hr2.rd, hr2.wr]; exact hin) hd hi hb) fun s'' ⟨hb', hz⟩ => ?_
    by_cases h32 : i + 1 = 32
    · exact .inl ⟨by rw [eval_ne, hz]; simp [h32], by rw [h32] at hb'; exact hb'⟩
    · exact .inr ⟨by rw [eval_ne, hz]; simp; omega, 32 - (i + 1), by omega, i + 1, rfl, by omega, hb'⟩
  -- The clamping.
  have hc3 := h3.ctx
  refine wp_mov (op2_imm (by decide)) fun s4 u4 => ?_
  have hc4 : VG.Proof.X25519.Arm.Ctx b s4 := hc3.of_rest (u4.rest (ws := [.r5]) (by decide)) (by decide)
  have st : ∀ (t : State), VG.Proof.X25519.Arm.Ctx b t → ∀ d, d < 4096 → State.addr (t.gpr .r0 + BitVec.ofNat 32 d) =
      State.addr b + BitVec.ofNat 64 d := fun t ht d hd => ht.ea hd
  refine wp_strb (a := State.addr b + BitVec.ofNat 64 BITS) (by decide) (st _ hc4 _ (by omega))
    (hc4.inW (by omega)) fun s5 u5 => ?_
  have hc5 : VG.Proof.X25519.Arm.Ctx b s5 := hc4.of_rest (u5.rest []) (by decide)
  refine wp_strb (a := State.addr b + BitVec.ofNat 64 (BITS + 1)) (by decide) (st _ hc5 _ (by omega))
    (hc5.inW (by omega)) fun s6 u6 => ?_
  have hc6 : VG.Proof.X25519.Arm.Ctx b s6 := hc5.of_rest (u6.rest []) (by decide)
  refine wp_strb (a := State.addr b + BitVec.ofNat 64 (BITS + 2)) (by decide) (st _ hc6 _ (by omega))
    (hc6.inW (by omega)) fun s7 u7 => ?_
  have hc7 : VG.Proof.X25519.Arm.Ctx b s7 := hc6.of_rest (u7.rest []) (by decide)
  refine wp_mov (op2_imm (by decide)) fun s8 u8 => ?_
  have hc8 : VG.Proof.X25519.Arm.Ctx b s8 := hc7.of_rest (u8.rest (ws := [.r5]) (by decide)) (by decide)
  refine wp_strb (a := State.addr b + BitVec.ofNat 64 (BITS + 254)) (by decide) (st _ hc8 _ (by omega))
    (hc8.inW (by omega)) fun s9 u9 => WP.block_nil ?_
  have v0 : (s4.gpr .r5).setWidth 8 = 0 := by rw [u4.gpr]; rfl
  have v1 : (s8.gpr .r5).setWidth 8 = 1 := by rw [u8.gpr]; rfl
  have hm9 : s9.mem = (((s3.mem.writeW (State.addr b + BitVec.ofNat 64 BITS) (0 : BitVec 8)).writeW
      (State.addr b + BitVec.ofNat 64 (BITS + 1)) (0 : BitVec 8)).writeW
      (State.addr b + BitVec.ofNat 64 (BITS + 2)) (0 : BitVec 8)).writeW
      (State.addr b + BitVec.ofNat 64 (BITS + 254)) (1 : BitVec 8) := by
    rw [u9.mem, v1, u8.mem, u7.mem, u6.gpr, u5.gpr, v0, u6.mem, u5.gpr, v0, u5.mem, v0, u4.mem]
  have ne : ∀ a c : Nat, a < 256 → c < 256 → a ≠ c →
      State.addr b + BitVec.ofNat 64 (BITS + a) ≠ State.addr b + BitVec.ofNat 64 (BITS + c) :=
    fun a c ha hc' hac => Offset.add_ofNat_ne _ (by omega) (by omega) (by omega)
  have hr9 : Rest [.r1, .r4, .r5, .r6, .r7] s s9 :=
    (hr2.mono (by decide)).trans ((h3.rest).trans ((u4.rest (by decide)).trans ((u5.rest _).trans
      ((u6.rest _).trans ((u7.rest _).trans ((u8.rest (by decide)).trans (u9.rest _)))))))
  refine ⟨hc3.of_rest ((u4.rest (ws := [.r5]) (by decide)).trans ((u5.rest _).trans ((u6.rest _).trans
    ((u7.rest _).trans ((u8.rest (by decide)).trans (u9.rest _)))))) (by decide), hr9, ?_, fun t ht => ?_⟩
  · rw [hm9, ← hm2]
    have m := List.mem_singleton_self (⟨State.addr b + BitVec.ofNat 64 BITS, 256⟩ : Region)
    refine ((((h3.frame.sub fun r hr => ⟨_, m, by
        rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega)⟩).writeW m _ ?_).writeW m _ ?_).writeW m _ ?_).writeW
      m _ ?_ <;> exact Offset.contains _ (n := 1) (by omega) (by omega) (by omega)
  · have hbit := VG.Proof.X25519.scalar_bit (length_bytesAt s.mem (State.addr sc) 32) ht
    rw [VG.Proof.X25519.Arm.getD_bytesAt _ _ (by omega)] at hbit
    rw [hbit, hm9]
    simp only [VG.WriteBytes.writeW8_apply]
    by_cases t254 : t = 254
    · subst t254; rw [VG.Proof.X25519.Arm.iteT rfl]; rfl
    rw [VG.Proof.X25519.Arm.iteF (ne _ _ (by omega) (by omega) t254)]
    by_cases t2 : t = 2
    · subst t2; rw [VG.Proof.X25519.Arm.iteT rfl]; rfl
    rw [VG.Proof.X25519.Arm.iteF (ne _ _ (by omega) (by omega) t2)]
    by_cases t1 : t = 1
    · subst t1; rw [VG.Proof.X25519.Arm.iteT rfl]; rfl
    rw [VG.Proof.X25519.Arm.iteF (ne _ _ (by omega) (by omega) t1)]
    by_cases t0 : t = 0
    · subst t0; rw [VG.Proof.X25519.Arm.iteT (by rfl)]; rfl
    rw [VG.Proof.X25519.Arm.iteF (show State.addr b + BitVec.ofNat 64 (BITS + t) ≠ State.addr b + BitVec.ofNat 64 BITS from
      fun e => ne t 0 (by omega) (by omega) t0 (by rw [e]; rfl)), h3.bits t (by omega), hm2,
      VG.Proof.X25519.Arm.iteF (show ¬ t < 3 by omega), VG.Proof.X25519.Arm.iteF t254]
    rfl

end

end VG.Proof.X25519.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.Arm.Lit`. -/
section

/-!
# X25519 on 32-bit ARM: the code as a literal

The code of `vg_x25519` as a literal (`materialize_code`,
`Proof/Framework/Lit.lean`).
-/

namespace VG

materialize_code Impl.X25519.Arm.x25519

end VG

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.Arm.CT`. -/
section

/-!
# X25519 on 32-bit ARM: constant time

Only the pointers in `r0`–`r3` are public; the taint analysis (`taint_decide`)
finds that every branch and address depends on them and on the loop counters
alone.
-/

namespace VG.Proof.X25519.Arm

open VG VG.Arm

theorem x25519_ct {Pre : State → Prop} {Pub : State → State → Prop}
    (hpub : ∀ s₁ s₂, Pre s₁ → Pre s₂ → Pub s₁ s₂ → ∀ r ∈ [Reg.r0, .r1, .r2, .r3], s₁.gpr r = s₂.gpr r) :
    ConstantTime isa Pre Pub Impl.X25519.Arm.x25519 :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2, .r3])
    (fun s₁ s₂ h₁ h₂ hp => Taint.agree_ofRegs (hpub s₁ s₂ h₁ h₂ hp)) (by taint_decide)

end VG.Proof.X25519.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.Arm.Main`. -/
section

/-!
# X25519 on 32-bit ARM: the whole function

`vg_x25519` writes `X25519(k, u)` to `out` (`x25519_correct`), restoring the
callee-saved registers.
-/

namespace VG.Proof.X25519.Arm

open VG VG.Arm VG.Impl.X25519.Arm
open VG.Spec.X25519 (P Fe bytesAt)
open VG.Proof.X25519 (leBytes toFe ladderAfter ladderAfter_swap_le)

/-- `vg_x25519(out = r0, scalar = r1, point = r2, scratch = r3)`. -/
def x25519Arm : Contract Arm.isa where
  pre s :=
    let out : Region := ⟨State.addr (s.gpr .r0), 32⟩
    let sc : Region := ⟨State.addr (s.gpr .r1), 32⟩
    let pt : Region := ⟨State.addr (s.gpr .r2), 32⟩
    let ws : Region := ⟨State.addr (s.gpr .r3), 4096⟩
    s.rd = [sc, pt] ∧ s.wr = [out, ws] ∧ out.Disjoint sc ∧ out.Disjoint pt ∧ out.Disjoint ws ∧
      sc.Disjoint ws ∧ pt.Disjoint ws ∧ (s.gpr .r0).toNat + 32 ≤ 2 ^ 32 ∧
      (s.gpr .r1).toNat + 32 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + 32 ≤ 2 ^ 32 ∧
      (s.gpr .r3).toNat + 4096 ≤ 2 ^ 32
  post s s' := bytesAt s'.mem (State.addr (s.gpr .r0)) 32 =
    VG.Spec.X25519.x25519 (bytesAt s.mem (State.addr (s.gpr .r1)) 32) (bytesAt s.mem (State.addr (s.gpr .r2)) 32)
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3

theorem XPre.of {s : State} (h : x25519Arm.pre s) : VG.Proof.X25519.Arm.XPre s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

section
variable {b : BitVec 32}

theorem lastSwap_ok {s : State} (hc : VG.Proof.X25519.Arm.Ctx b s) {sw : Nat} (hsw : sw ≤ 1)
    (h10 : s.gpr .r10 = BitVec.ofNat 32 sw) {v : Nat → Fe} (hS : VG.Proof.X25519.Arm.SlotsOk s.mem (State.addr b) VG.Proof.X25519.Arm.LQ v) :
    WP isa (.block lastSwap) s fun s' => VG.Proof.X25519.Arm.Stp b s s' ∧ VG.Proof.X25519.Arm.Ctx b s' ∧
      VG.Proof.X25519.Arm.SlotsOk s'.mem (State.addr b) VG.Proof.X25519.Arm.LQ (VG.Proof.X25519.Arm.swapV Z2 Z3 sw (VG.Proof.X25519.Arm.swapV X2 X3 sw v)) := by
  simp only [lastSwap, mask, List.cons_append, List.nil_append]
  refine wp_mov (op2_imm (by decide)) fun s1 u1 => wp_dp (op2_reg _ _) fun s2 u2 => ?_
  have hr2 : Rest [.r9] s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  have hc2 : VG.Proof.X25519.Arm.Ctx b s2 := hc.of_rest hr2 (by decide)
  have e9 : s2.gpr .r9 = 0 - BitVec.ofNat 32 sw := by
    rw [u2.gpr]; show s1.gpr .r9 - s1.gpr .r10 = _
    rw [u1.gpr, u1.other _ (by decide), h10]
  have hm2 : s2.mem = s.mem := by rw [u2.mem, u1.mem]
  refine WP.append (VG.Proof.X25519.Arm.cswapS (acc := ACC) (qs := VG.Proof.X25519.Arm.LQ) (v := v) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) hc2
    hsw e9 (by rw [hm2]; exact hS)) fun s3 ⟨hr3, hf3, hS3⟩ => ?_
  have hc3 : VG.Proof.X25519.Arm.Ctx b s3 := hc2.of_rest hr3 (by decide)
  refine WP.mono (VG.Proof.X25519.Arm.cswapS (acc := ACC) (qs := VG.Proof.X25519.Arm.LQ) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) hc3 hsw
    (by rw [hr3.gpr _ (by decide), e9]) hS3) fun s4 ⟨hr4, hf4, hS4⟩ =>
    ⟨⟨(hr2.mono (by decide)).trans ((hr3.mono (by decide)).trans (hr4.mono (by decide))),
      by rw [← hm2]; exact hf3.trans hf4⟩, hc3.of_rest hr4 (by decide), hS4⟩

theorem restore_ok {s : State} (hc : VG.Proof.X25519.Arm.Ctx b s) {g : Reg → BitVec 32} (hs : VG.Proof.X25519.Arm.Saved (State.addr b) g s.mem) :
    WP isa (.block restore) s fun s' => (∀ i < 8, s'.gpr (savedReg i) = g (savedReg i)) ∧
      Rest [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11] s s' ∧ s'.mem = s.mem := by
  have hsr : ∀ i < 8, savedReg i ∈ [Reg.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11] := by decide
  have hinj : ∀ i < 8, ∀ j < 8, savedReg i = savedReg j → i = j := by decide
  have h0 : ∀ i < 8, savedReg i ≠ .r0 := by decide
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun n s' => (∀ i < n, s'.gpr (savedReg i) = g (savedReg i)) ∧
      Rest [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11] s s' ∧ s'.mem = s.mem)
    (fun n s' hn ⟨hl, hr, hm⟩ => ?_) 8 (Nat.le_refl _) s
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), Rest.refl _ _, rfl⟩) fun s' h => h
  refine VG.Proof.X25519.Arm.ldr0_ok (hc.of_rest hr (by decide)) (d := 4 * n) (by omega) fun s1 u1 =>
    WP.block_nil ⟨fun i hi => ?_, hr.trans (u1.rest (hsr n hn)), by rw [u1.mem, hm]⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h' | rfl
  · rw [u1.other _ (fun e => absurd (hinj _ (by omega) _ hn e) (by omega))]; exact hl i h'
  · rw [u1.gpr, hm, hs i hn]

/-- The saved registers stay where no code writes. -/
theorem Saved.frame {g : Reg → BitVec 32} {m m' : Mem} (hs : VG.Proof.X25519.Arm.Saved (State.addr b) g m) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, ∀ i < 8, Region.Disjoint ⟨State.addr b + BitVec.ofNat 64 (4 * i), 4⟩ r) :
    VG.Proof.X25519.Arm.Saved (State.addr b) g m' := fun i hi => by
  rw [hf.readW (Region.contains_self _ _) (fun r hr => hd r hr i hi) (by decide)]; exact hs i hi

theorem FA_saved (i : Nat) (hi : i < 8) :
    Region.Disjoint ⟨State.addr b + BitVec.ofNat 64 (4 * i), 4⟩ (VG.Proof.X25519.Arm.FA ACC b) :=
  Offset.disjoint _ (.inl (by omega)) (by omega) (by rw [VG.Proof.X25519.Arm.ACC_eq]; omega)

/-- The slots stay through a write of `BITS`. -/
theorem SlotsOk.bits {m m' : Mem} {qs : List Nat} {v : Nat → Fe} (hS : VG.Proof.X25519.Arm.SlotsOk m (State.addr b) qs v)
    (hq : (qs.all fun q => q + 64 ≤ BITS) = true)
    (hf : Frame [⟨State.addr b + BitVec.ofNat 64 BITS, 256⟩] m m') : VG.Proof.X25519.Arm.SlotsOk m' (State.addr b) qs v := by
  intro q hq'
  have h := List.all_eq_true.mp hq q hq'
  simp only [decide_eq_true_eq] at h
  have hB : BITS = 1280 := rfl
  have e := VG.Proof.X25519.Arm.limb_frame (o := q) hf fun r hr k hk => by
    rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
  exact ⟨fun k hk => by rw [e k hk]; exact (hS q hq').1 k hk, by rw [VG.Proof.X25519.Arm.FS, VG.Proof.X25519.Arm.V, val16_congr e]; exact (hS q hq').2⟩

end

theorem bytesAt_frame {m m' : Mem} {rs : List Region} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, 32⟩ r) : bytesAt m' p 32 = bytesAt m p 32 := by
  simp only [bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  exact hf _ fun r hr hc => hd r hr _ (Offset.contains_base _ (by omega) (by omega)) hc

theorem x25519_correct {s : State} (hp : VG.Proof.X25519.Arm.XPre s) :
    WP isa x25519 s fun s' => abiPreserved s s' ∧ x25519Arm.post s s' := by
  have hfit := hp.f3
  have hB : BITS = 1280 := rfl
  have hsc_in : (⟨State.addr (s.gpr .r1), 32⟩ : Region) ∈ s.rd ++ s.wr := by rw [hp.rd]; simp
  unfold x25519
  refine WP.seq (WP.mono (VG.Proof.X25519.Arm.setup_ok hp) fun s1 ⟨hc1, h12, h1, hsv1, hf1, hS1, hr1⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.X25519.Arm.bits_ok hc1 h1 hp.f1 (by rw [hr1.rd, hr1.wr]; exact hsc_in) hp.sc_ws)
    fun s2 ⟨hc2, hr2, hf2, hb2⟩ => ?_)
  have hS2 := hS1.bits (by decide) hf2
  refine WP.seq (WP.mono (VG.Proof.X25519.Arm.ladder_ok hc2 hb2 hS2) fun s3 ⟨hst3, hc3, h10, hS3⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.X25519.Arm.lastSwap_ok hc3 (ladderAfter_swap_le _ _ (by decide)) h10 hS3)
    fun s4 ⟨hst4, hc4, hS4⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.X25519.Arm.invert_ok hc4 (hS4.mono (by decide)) rfl) fun s5 ⟨hst5, hc5, hS5⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.X25519.Arm.mulS (acc := ACC) (o := X2) (x := X2) (y := R) (by decide) (by decide) (by decide)
    (by decide) (by decide) hc5 hS5)
    fun s6 ⟨hr6, hf6, hS6⟩ => ?_)
  -- The registers and regions along the way.
  have hst6 : VG.Proof.X25519.Arm.Stp (s.gpr .r3) s2 s6 := hst3.trans (hst4.trans (hst5.trans ⟨hr6.mono (by decide), hf6⟩))
  have h12' : s6.gpr .r12 = s.gpr .r0 := by
    rw [hst6.rest.gpr _ (by decide), hr2.gpr _ (by decide), h12]
  have hwr6 : s6.wr = s.wr := by rw [hst6.rest.wr, hr2.wr, hr1.wr]
  have hc6 : VG.Proof.X25519.Arm.Ctx (s.gpr .r3) s6 := hc5.of_rest hr6 (by decide)
  refine WP.append (VG.Proof.X25519.Arm.freeze_ok hc6 (hS6 X2 (by decide)).1 h12' (by rw [hwr6, hp.wr]; simp) hp.f0
    hp.out_ws.symm) fun s7 ⟨hbytes, hr7, hf7⟩ => ?_
  have hc7 : VG.Proof.X25519.Arm.Ctx (s.gpr .r3) s7 := hc6.of_rest hr7 (by decide)
  -- The saved registers.
  have hsv7 : VG.Proof.X25519.Arm.Saved (State.addr (s.gpr .r3)) s.gpr s7.mem := by
    refine ((hsv1.frame hf2 fun r hr i hi => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by decide)).frame
      hst6.frame fun r hr i hi => by rw [List.mem_singleton.mp hr]; exact VG.Proof.X25519.Arm.FA_saved i hi).frame hf7 fun r hr i hi => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact VG.Proof.X25519.Arm.FA_saved i hi
    · exact (hp.out_ws.symm.sub_left (Offset.sub_base _ (by omega))).symm.symm
  refine WP.mono (VG.Proof.X25519.Arm.restore_ok hc7 hsv7) fun s8 ⟨hg8, hr8, hm8⟩ => ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hg8 0 (by decide)
    · exact hg8 1 (by decide)
    · exact hg8 2 (by decide)
    · exact hg8 3 (by decide)
    · exact hg8 4 (by decide)
    · exact hg8 5 (by decide)
    · exact hg8 6 (by decide)
    · exact hg8 7 (by decide)
    · rw [hr8.gpr _ (by decide), hr7.gpr _ (by decide), hst6.rest.gpr _ (by decide), hr2.gpr _ (by decide),
        hr1.gpr _ (by decide)]
  · rw [hr8.sp, hr7.sp, hst6.rest.sp, hr2.sp, hr1.sp]
  · -- The result.
    show bytesAt s8.mem _ 32 = _
    rw [hm8, hbytes, VG.Proof.X25519.x25519_eq]
    -- The scalar and the u-coordinate, as read by `bits` and `setup`.
    have hk : bytesAt s1.mem (State.addr (s.gpr .r1)) 32 = bytesAt s.mem (State.addr (s.gpr .r1)) 32 :=
      VG.Proof.X25519.Arm.bytesAt_frame hf1 fun r hr => by rw [List.mem_singleton.mp hr]; exact hp.sc_ws
    rw [hk] at hS3 h10 hS4 hS5 hS6
    have e6 : VG.Proof.X25519.Arm.FS s6.mem (State.addr (s.gpr .r3)) X2 = _ := (hS6 X2 (by decide)).2
    rw [← VG.Proof.X25519.toFe_val, ← VG.Proof.X25519.encodeUCoordinate_eq]
    change VG.Spec.X25519.encodeUCoordinate (VG.Proof.X25519.Arm.FS s6.mem (State.addr (s.gpr .r3)) X2) = _
    rw [e6]
    simp only [VG.Proof.X25519.Arm.upd, VG.Proof.X25519.Arm.swapV, VG.Proof.X25519.Arm.ladV, sel, VG.Proof.X25519.Arm.iteT, VG.Proof.X25519.invert_eq, VG.Proof.X25519.pow_pw, VG.Proof.X25519.Arm.cswap_fst,
      VG.Proof.X25519.Arm.uOf, X1, X2, Z2, X3, Z3, R, Nat.reduceEqDiff, ite_false]

end VG.Proof.X25519.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.Arm.Verified`. -/
section

/-!
# X25519 on 32-bit ARM: verified

`vg_x25519` meets the shared contract of `Spec/X25519/Contract.lean`: the
proof against `x25519Arm`, which it implies, and a state satisfying it.
-/

namespace VG.Proof.X25519.Arm

open VG VG.Arm

theorem x25519_ok (s : State) (hs : x25519Arm.pre s) :
    ∃ t s', Exec isa Impl.X25519.Arm.x25519 s t s' ∧ abiPreserved s s' ∧ x25519Arm.post s s' :=
  VG.Proof.X25519.Arm.x25519_correct (XPre.of hs)

theorem x25519_ct' : ConstantTime isa x25519Arm.pre x25519Arm.pub Impl.X25519.Arm.x25519 :=
  VG.Proof.X25519.Arm.x25519_ct fun _ _ _ _ ⟨_, h0, h1, h2, h3⟩ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

/-- A state satisfying the precondition. -/
def x25519Sat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | .r3 => 0x4000 | _ => 0
  sp := 0x10000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x2000, 32⟩, ⟨0x3000, 32⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x4000, 4096⟩]

theorem x25519_verified :
    Verified Arm.target Impl.X25519.Arm.x25519 (Spec.X25519.x25519Contract Arm.abi) :=
  Verified.of_correct VG.Proof.X25519.Arm.x25519_ok VG.Proof.X25519.Arm.x25519_ct' (by
    sig_implies [Spec.X25519.x25519Contract, Spec.X25519.x25519Sig, Proof.X25519.Arm.x25519Arm, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [Proof.X25519.Arm.x25519Sat,
      Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using Proof.X25519.Arm.x25519Sat)

end VG.Proof.X25519.Arm

end
