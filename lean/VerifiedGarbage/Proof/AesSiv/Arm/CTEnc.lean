import VerifiedGarbage.Proof.AesSiv.Arm.CTCtr
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-!
# AES-SIV on ARMv7: `encrypt` and `decrypt` are constant time

Untrusted: everything here is checked by Lean. Two runs with the same
public arguments and the same descriptors of the components (`E0`) leak the
same. The blocks reading the stack arguments are checked by the taint
analysis with them public (`CT.argTaint`); between the pieces, the
correctness lemmas give each run the next piece's invariant (`CtrI` for the
pieces after S2V of the associated data, which keep the stack arguments);
`decrypt` compares the IVs and masks the data without a branch, so nothing
it does depends on the result.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesSiv.Arm

open VG VG.Arm VG.Impl.AesSiv.Arm
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesCcm.Arm (blw)
open VG.Proof.AesGcm.Arm (CT savedR in_off bytesAt_frame Keeps)
open VG.Proof.MdStream.Arm (wp_ldrSp)

/-- The entry, with the regions the code may write apart from the stack
arguments, and the descriptors' words `dsc`. -/
structure E0 (c w sp a D T : BitVec 32) (R N n : Nat) (dsc : Nat → Nat → BitVec 32) (s : State) : Prop where
  pre : EPre c w sp a D T R N n s
  wa : ∀ r ∈ s.wr, (⟨State.addr sp, 16⟩ : Region).Disjoint r
  desc : DescEq s.mem a N dsc

/-- The descriptors' words, after writes apart from them. -/
theorem DescEq.frame {m m' : Mem} {a : BitVec 32} {N : Nat} {dsc : Nat → Nat → BitVec 32}
    (h : DescEq m a N dsc) {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (⟨State.addr a, 8 * N⟩ : Region).Disjoint r) : DescEq m' a N dsc := fun i hi j hj => by
  rw [← h i hi j hj]
  exact hf.readW (r := ⟨State.addr a + BitVec.ofNat 64 (8 * i + 4 * j), 4⟩) (Region.contains_self _ _)
    (fun r hr => (hd r hr).sub_left (Offset.sub_base _ (by omega))) (by decide)

/-- After code that keeps the stack arguments: writes apart from them, the
same regions and an environment. -/
theorem CtrI.next {c w sp D : BitVec 32} {R n : Nat} {s s' : State} (h : CtrI c w sp R D n s)
    (he : Env c w sp R s') (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) {rs : List Region}
    (hf : Frame rs s.mem s'.mem) (hd : ∀ r ∈ rs, (⟨State.addr sp, 16⟩ : Region).Disjoint r) :
    CtrI c w sp R D n s' where
  env := he
  dat := h.dat.of_eq hrd hwr
  wa := by rw [hwr]; exact h.wa
  afit := h.afit
  args := by rw [hrd, hwr]; exact h.args
  args_w := h.args_w
  args_d := h.args_d
  m0 := by
    rw [hf.readW (r := ⟨State.addr sp, 4⟩) (Region.contains_self _ _)
      (fun r hr => (hd r hr).sub_left (Region.sub_prefix (by decide))) (by decide), h.m0]
  m1 := by
    rw [hf.readW (r := ⟨State.addr sp + BitVec.ofNat 64 4, 4⟩) (Region.contains_self _ _)
      (fun r hr => (hd r hr).sub_left (Offset.sub_base _ (by decide))) (by decide), h.m1]
  n32 := h.n32

/-- `siv`, the third stack argument, at `T`: 16 bytes apart from `W` that the
code may read. -/
structure SivA (w sp T : BitVec 32) (s : State) : Prop where
  m2 : s.mem.readW (State.addr sp + BitVec.ofNat 64 8) 32 = T
  fit : T.toNat + 16 ≤ 2 ^ 32
  rd : Covers [⟨State.addr T, 16⟩] (s.rd ++ s.wr)
  t_w : (⟨State.addr T, 16⟩ : Region).Disjoint ⟨State.addr w, 2576⟩

theorem SivA.of_pre {c w sp a D T : BitVec 32} {R N n : Nat} {s : State} (h : EPre c w sp a D T R N n s) :
    SivA w sp T s :=
  ⟨h.a2, h.tfit, h.t_rd, h.t_w⟩

/-- `siv` where it was, after writes apart from the stack arguments. -/
theorem SivA.next {w sp T : BitVec 32} {s s' : State} (h : SivA w sp T s) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hd : ∀ r ∈ rs, (⟨State.addr sp, 16⟩ : Region).Disjoint r) : SivA w sp T s' where
  m2 := by
    rw [hf.readW (r := ⟨State.addr sp + BitVec.ofNat 64 8, 4⟩) (Region.contains_self _ _)
      (fun r hr => (hd r hr).sub_left (Offset.sub_base _ (by decide))) (by decide), h.m2]
  fit := h.fit
  rd := by rw [hrd, hwr]; exact h.rd
  t_w := h.t_w

/-- The third stack argument: `siv`'s address. -/
theorem SivA.arg {c w sp D T : BitVec 32} {R n : Nat} {s : State} (hc : CtrI c w sp R D n s)
    (h : SivA w sp T s) : stackArg s 2 = T := by
  rw [stackArg, stackArgAddr, hc.env.sp, addr_add (by have := hc.afit; omega), h.m2]

section
variable {c w sp : BitVec 32} {R : Nat} (L : Lay c w sp) (hR : R = 10 ∨ R = 12 ∨ R = 14)
include L hR

omit L hR in
/-- A region of `W` but its first 16 bytes, or the stack below `sp`, is apart
from the stack arguments. -/
theorem args_dis (hw : (⟨State.addr sp, 16⟩ : Region).Disjoint ⟨State.addr w, 2576⟩) :
    ∀ r ∈ savedR w :: wR w sp, (⟨State.addr sp, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact Offset.base_disjoint_below (State.addr sp) (n := 16) (k := 16) (by decide)

omit L hR in
/-- What S2V's end writes, apart from the stack arguments. -/
theorem args_dis_oR (hw : (⟨State.addr sp, 16⟩ : Region).Disjoint ⟨State.addr w, 2576⟩) {out : Nat}
    (hout : out = 0 ∨ out = tOff) : ∀ r ∈ oR w sp out, (⟨State.addr sp, 16⟩ : Region).Disjoint r := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact hw.sub_right (Lay.wSub (by rcases hout with rfl | rfl <;> decide))
  · exact args_dis hw r (List.mem_cons_of_mem _ hr)

omit L hR in
/-- What CTR writes, apart from the stack arguments. -/
theorem args_dis_ctr {D : BitVec 32} {n : Nat}
    (hw : (⟨State.addr sp, 16⟩ : Region).Disjoint ⟨State.addr w, 2576⟩)
    (hd : (⟨State.addr sp, 16⟩ : Region).Disjoint ⟨State.addr D, n⟩) :
    ∀ r ∈ ctrR w sp D n, (⟨State.addr sp, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact Offset.base_disjoint_below (State.addr sp) (n := 16) (k := 16) (by decide)
  · exact hd

omit L hR in
/-- The pieces' invariant, from the entry, after writes that keep the stack
arguments. -/
theorem CtrI.of_entry {a D T : BitVec 32} {N n : Nat} {dsc : Nat → Nat → BitVec 32} {σ s : State}
    (h : E0 c w sp a D T R N n dsc σ) (he : Env c w sp R s) (hrd : s.rd = σ.rd) (hwr : s.wr = σ.wr)
    {rs : List Region} (hf : Frame rs σ.mem s.mem) (hd : ∀ r ∈ rs, (⟨State.addr sp, 16⟩ : Region).Disjoint r) :
    CtrI c w sp R D n s where
  env := he
  dat := h.pre.data.of_eq hrd hwr
  wa := by rw [hwr]; exact h.wa
  afit := h.pre.afit
  args := by rw [hrd, hwr]; exact h.pre.args
  args_w := h.pre.args_w
  args_d := h.pre.args_d
  m0 := by
    rw [hf.readW (r := ⟨State.addr sp, 4⟩) (Region.contains_self _ _)
      (fun r hr => (hd r hr).sub_left (Region.sub_prefix (by decide))) (by decide), h.pre.a0]
  m1 := by
    rw [hf.readW (r := ⟨State.addr sp + BitVec.ofNat 64 4, 4⟩) (Region.contains_self _ _)
      (fun r hr => (hd r hr).sub_left (Offset.sub_base _ (by decide))) (by decide), h.pre.a1]
  n32 := h.pre.n32

omit L hR in
/-- The data's address and length from the stack arguments. -/
theorem loadArgs_ct {D : BitVec 32} {n : Nat} :
    CT (CtrI c w sp R D n) (.block [.ldrSp .r6 0, .ldrSp .r5 4]) := by
  obtain ⟨_, hA⟩ : ∃ h, (Taint.check VG.Arm.taint (argTaint [] (4 * 2))
      (.block [.ldrSp .r6 0, .ldrSp .r5 4]) h).isSome = true := ⟨_, by taint_decide⟩
  exact CT.argTaint _ _ (fun _ _ _ _ r hr => by simp at hr) (fun s₁ s₂ h₁ h₂ => by rw [h₁.env.sp, h₂.env.sp])
    (fun s h => ⟨by rw [h.env.sp]; have := h.afit; omega, fun r hr => by
      rw [h.env.sp]; exact (h.wa r hr).sub_left (Region.sub_prefix (by decide))⟩)
    (fun s₁ s₂ h₁ h₂ => argMem_of (by rw [h₁.env.sp, h₂.env.sp]) (by rw [h₁.env.sp]; have := h₁.afit; omega)
      fun i hi => by
        rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
        · rw [h₁.arg.1, h₂.arg.1]
        · rw [h₁.arg.2, h₂.arg.2]) hA

omit L hR in
theorem loadArgs_wp {D : BitVec 32} {n : Nat} {s : State} (h : CtrI c w sp R D n s) :
    WP isa (.block [.ldrSp .r6 0, .ldrSp .r5 4]) s fun s' => (CtrI c w sp R D n s' ∧ s'.gpr .r6 = D ∧
      s'.gpr .r5 = BitVec.ofNat 32 n) ∧ s'.gpr .r0 = s.gpr .r0 := by
  have hsp := h.env.sp
  refine wp_ldrSp (a := State.addr sp + BitVec.ofNat 64 0) (by decide)
    (by rw [hsp]; exact addr_add (by have := h.afit; omega)) (in_off h.args (by decide) (by decide))
    fun s₁ u₁ => ?_
  refine wp_ldrSp (a := State.addr sp + BitVec.ofNat 64 4) (by decide)
    (by rw [u₁.sp, hsp]; exact addr_add (by have := h.afit; omega))
    (by rw [u₁.rd, u₁.wr]; exact in_off h.args (by decide) (by decide)) fun s₂ u₂ => WP.block_nil ?_
  have he : Env c w sp R s₂ := h.env.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> rw [u₂.other _ (by decide), u₁.other _ (by decide)])
    (by rw [u₂.sp, u₁.sp]) (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr])
  refine ⟨⟨h.next he (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr]) (rs := [])
      (by rw [u₂.mem, u₁.mem]; exact Frame.refl _ _) (fun _ hr => by simp at hr), ?_, ?_⟩,
    by rw [u₂.other _ (by decide), u₁.other _ (by decide)]⟩
  · rw [u₂.other _ (by decide), u₁.gpr, BitVec.add_zero, h.m0]
  · rw [u₂.gpr, u₁.mem, h.m1]

/-! ## S2V of the associated data -/

/-- Between S2V's pieces, in one run: from the entry `σ`, the memory `m₀`
after the save, before component `i`. -/
def SI (c w sp a D T : BitVec 32) (R N n : Nat) (dsc : Nat → Nat → BitVec 32) (i : Nat) (s : State) : Prop :=
  ∃ σ m₀, E0 c w sp a D T R N n dsc σ ∧ Frame [savedR w] σ.mem m₀ ∧ AInv c w sp a R N m₀ σ i s ∧
    DescEq m₀ a N dsc

theorem encS2v_ct {a D T : BitVec 32} {N n : Nat} {dsc : Nat → Nat → BitVec 32} (hN : N < 2 ^ 32) :
    CT (E0 c w sp a D T R N n dsc) encS2v := by
  obtain ⟨_, hA⟩ : ∃ h, (Taint.check VG.Arm.taint (argTaint [.r0, .r1, .r2, .r3] (4 * 4))
      (.block (encPre ++ startPre)) h).isSome = true := ⟨_, by taint_decide⟩
  have ab : CT (E0 c w sp a D T R N n dsc) (.seq (.block (encPre ++ startPre)) finFrame) := by
    refine CT.seq (J := fun s => ∃ σ mₛ, Started c w sp a R N σ mₛ s)
      (CT.argTaint _ _ (fun s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · rw [h₁.pre.r0, h₂.pre.r0]
        · rw [h₁.pre.r1, h₂.pre.r1]
        · rw [h₁.pre.r2, h₂.pre.r2]
        · rw [h₁.pre.r3, h₂.pre.r3]) (fun s₁ s₂ h₁ h₂ => by rw [h₁.pre.hsp, h₂.pre.hsp])
        (fun s h => ⟨by rw [h.pre.hsp]; exact h.pre.afit, fun r hr => by
          rw [h.pre.hsp]; exact h.wa r hr⟩)
        (fun s₁ s₂ h₁ h₂ => argMem_of (by rw [h₁.pre.hsp, h₂.pre.hsp]) (by rw [h₁.pre.hsp]; exact h₁.pre.afit)
          fun i hi => by
            have e : ∀ {s : State}, E0 c w sp a D T R N n dsc s → ∀ {k : Nat}, k < 4 →
                stackArg s k = s.mem.readW (State.addr sp + BitVec.ofNat 64 (4 * k)) 32 := fun h k hk => by
              rw [stackArg, stackArgAddr, h.pre.hsp, addr_add (by have := h.pre.afit; omega)]
            rw [e h₁ hi, e h₂ hi]
            rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl
            · rw [show 4 * 0 = 0 from rfl, BitVec.add_zero, h₁.pre.a0, h₂.pre.a0]
            · rw [h₁.pre.a1, h₂.pre.a1]
            · rw [h₁.pre.a2, h₂.pre.a2]
            · rw [h₁.pre.a3, h₂.pre.a3]) hA)
      (fun s h => WP.mono (startBlock_ok L h.pre) fun s' ⟨mₛ, St⟩ => ⟨s, mₛ, St⟩) ?_
    exact fin_rel fun s₁ s₂ hh => by
      obtain ⟨⟨_, _, h₁⟩, ⟨_, _, h₂⟩⟩ := hh
      exact ⟨h₁.args, h₂.args, h₁.env.sp, h₂.env.sp⟩
  refine RelCT.assoc (CT.seq ab (J := SI c w sp a D T R N n dsc 0) (fun s h => WP.mono (start_ok L h.pre)
    fun s' ⟨mₛ, fs, _, I⟩ => ⟨s, mₛ, h, fs, I, h.desc.frame fs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.pre.ads.dw.sub_right (Lay.wSub (by decide))⟩) ?_)
  refine CT.seq (J := SI c w sp a D T R N n dsc N)
    ((s2vAds_ct L hR hN).mono fun s ⟨σ, m₀, _, _, I, hd⟩ => ⟨m₀, σ, I, hd⟩)
    (fun s ⟨σ, m₀, h, fs, I, hd⟩ => WP.mono (s2vAds_ok L hR I hN) fun s' I' => ⟨σ, m₀, h, fs, I', hd⟩) ?_
  exact (loadArgs_ct (c := c) (w := w) (sp := sp) (R := R) (D := D) (n := n)).mono fun s ⟨σ, m₀, h, fs, I, _⟩ =>
    CtrI.of_entry h I.env I.rd I.wr ((fs.mono (by simp)).trans (I.frame.mono fun r hr =>
      List.mem_cons_of_mem _ hr)) (args_dis h.pre.args_w)

omit hR in
/-- After S2V of the associated data. -/
theorem encS2v_wp {a D T : BitVec 32} {N n : Nat} {dsc : Nat → Nat → BitVec 32} {s : State}
    (h : E0 c w sp a D T R N n dsc s) :
    WP isa encS2v s fun s' => (CtrI c w sp R D n s' ∧ s'.gpr .r6 = D ∧ s'.gpr .r5 = BitVec.ofNat 32 n) ∧
      SivA w sp T s' ∧ s'.wr = s.wr :=
  WP.mono (s2v_ok L h.pre) fun s' ⟨mₛ, O⟩ => by
    have F : Frame (savedR w :: wR w sp) s.mem s'.mem :=
      (O.fs.mono (by simp)).trans (O.frame.mono fun r hr => List.mem_cons_of_mem _ hr)
    exact ⟨⟨CtrI.of_entry h O.env O.rd O.wr F (args_dis h.pre.args_w), O.r6, O.r5⟩,
      (SivA.of_pre h.pre).next O.rd O.wr F (args_dis h.pre.args_w), O.wr⟩

/-! ## `siv` -/

omit hR in
/-- The IV copied to `siv`, which the code may write: what follows needs only
the environment. -/
theorem sivOut_wp {D T : BitVec 32} {n : Nat} {s : State}
    (h : CtrI c w sp R D n s ∧ SivA w sp T s ∧ Covers [⟨State.addr T, 16⟩] s.wr) :
    WP isa (.block sivOut) s (Env c w sp R) := by
  obtain ⟨hc, ht, hw⟩ := h
  have a8 : State.addr (s.sp + BitVec.ofNat 32 8) = State.addr sp + BitVec.ofNat 64 8 := by
    rw [hc.env.sp]; exact addr_add (by have := hc.afit; omega)
  obtain ⟨s', run, -, -, g, rd, wr, sp'⟩ := sivOut_ok L hc.env (T := T)
    (by rw [a8]; exact in_off hc.args (by decide) (by decide)) (by rw [a8]; exact ht.m2) hw ht.fit
    (ht.t_w.sub_right (Region.sub_prefix (by decide)))
  exact WP.of_runBlock ⟨s', run, hc.env.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact g _ (by decide) (by decide)) sp' rd wr⟩

omit L hR in
theorem sivOut_ct {D T : BitVec 32} {n : Nat} :
    CT (fun s => CtrI c w sp R D n s ∧ SivA w sp T s ∧ Covers [⟨State.addr T, 16⟩] s.wr) (.block sivOut) := by
  obtain ⟨_, hA⟩ : ∃ h, (Taint.check VG.Arm.taint (argTaint [.r11] (4 * 3)) (.block sivOut) h).isSome = true :=
    ⟨_, by taint_decide⟩
  exact CT.argTaint _ _ (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.env.r11, h₂.1.env.r11])
    (fun s₁ s₂ h₁ h₂ => by rw [h₁.1.env.sp, h₂.1.env.sp])
    (fun s h => ⟨by rw [h.1.env.sp]; have := h.1.afit; omega, fun r hr => by
      rw [h.1.env.sp]; exact (h.1.wa r hr).sub_left (Region.sub_prefix (by decide))⟩)
    (fun s₁ s₂ h₁ h₂ => argMem_of (by rw [h₁.1.env.sp, h₂.1.env.sp]) (by rw [h₁.1.env.sp]; have := h₁.1.afit; omega)
      fun i hi => by
        rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
        · rw [h₁.1.arg.1, h₂.1.arg.1]
        · rw [h₁.1.arg.2, h₂.1.arg.2]
        · rw [SivA.arg h₁.1 h₁.2.1, SivA.arg h₂.1 h₂.2.1]) hA

omit hR in
/-- The received IV copied from `siv` to `W`. -/
theorem sivIn_wp {D T : BitVec 32} {n : Nat} {s : State} (h : CtrI c w sp R D n s ∧ SivA w sp T s) :
    WP isa (.block sivIn) s (CtrI c w sp R D n) := by
  obtain ⟨hc, ht⟩ := h
  have a8 : State.addr (s.sp + BitVec.ofNat 32 8) = State.addr sp + BitVec.ofNat 64 8 := by
    rw [hc.env.sp]; exact addr_add (by have := hc.afit; omega)
  obtain ⟨s', run, -, f, g, rd, wr, sp'⟩ := sivIn_ok L hc.env (T := T)
    (by rw [a8]; exact in_off hc.args (by decide) (by decide)) (by rw [a8]; exact ht.m2) ht.rd ht.fit
    (ht.t_w.sub_right (Region.sub_prefix (by decide)))
  refine WP.of_runBlock ⟨s', run, hc.next (hc.env.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact g _ (by decide) (by decide)) sp' rd wr) rd wr f fun r hr => ?_⟩
  simp only [List.mem_singleton] at hr; subst hr
  exact hc.args_w.sub_right (Region.sub_prefix (by decide))

omit L hR in
theorem sivIn_ct {D T : BitVec 32} {n : Nat} :
    CT (fun s => CtrI c w sp R D n s ∧ SivA w sp T s) (.block sivIn) := by
  obtain ⟨_, hA⟩ : ∃ h, (Taint.check VG.Arm.taint (argTaint [.r11] (4 * 3)) (.block sivIn) h).isSome = true :=
    ⟨_, by taint_decide⟩
  exact CT.argTaint _ _ (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.env.r11, h₂.1.env.r11])
    (fun s₁ s₂ h₁ h₂ => by rw [h₁.1.env.sp, h₂.1.env.sp])
    (fun s h => ⟨by rw [h.1.env.sp]; have := h.1.afit; omega, fun r hr => by
      rw [h.1.env.sp]; exact (h.1.wa r hr).sub_left (Region.sub_prefix (by decide))⟩)
    (fun s₁ s₂ h₁ h₂ => argMem_of (by rw [h₁.1.env.sp, h₂.1.env.sp]) (by rw [h₁.1.env.sp]; have := h₁.1.afit; omega)
      fun i hi => by
        rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
        · rw [h₁.1.arg.1, h₂.1.arg.1]
        · rw [h₁.1.arg.2, h₂.1.arg.2]
        · rw [SivA.arg h₁.1 h₁.2, SivA.arg h₂.1 h₂.2]) hA

/-! ## The ends -/

omit L hR in
theorem restore_ct : CT (Env c w sp R) (.block Impl.AesGcm.Arm.restore) := by
  obtain ⟨_, hA⟩ : ∃ h, (Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs [.r11])
      (.block Impl.AesGcm.Arm.restore) h).isSome = true := ⟨_, by taint_decide⟩
  exact CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁.r11, h₂.r11]) hA

/-- S2V's end with the data into `W + out`, from the pieces' invariant with
the data in `r6` and `r5`. -/
theorem finish_next {D : BitVec 32} {n : Nat} {out : Nat} (hout : out = 0 ∨ out = tOff) {s : State}
    (h : CtrI c w sp R D n s ∧ s.gpr .r6 = D ∧ s.gpr .r5 = BitVec.ofNat 32 n)
    (hA : ∀ r ∈ oR w sp out, (⟨State.addr sp, 16⟩ : Region).Disjoint r) :
    WP isa (finish out) s (CtrI c w sp R D n) := by
  exact WP.mono (finish_ok L h.1.env hR h.1.dat.buf h.1.n32 h.2.1 h.2.2 hout) fun s' ⟨he, rd, wr, _, f, _⟩ =>
    h.1.next he rd wr f hA

omit L hR in
/-- The IVs compared, and the data's address and length loaded again. -/
theorem cmpLoad_ct {D : BitVec 32} {n : Nat} :
    CT (CtrI c w sp R D n) (.block (compare ++ ([.ldrSp .r6 0, .ldrSp .r5 4] : List Instr))) := by
  obtain ⟨_, hA⟩ : ∃ h, (Taint.check VG.Arm.taint (argTaint [.r9, .r10, .r11] (4 * 2))
      (.block (compare ++ [.ldrSp .r6 0, .ldrSp .r5 4])) h).isSome = true := ⟨_, by taint_decide⟩
  exact CT.argTaint _ _ (fun s₁ s₂ h₁ h₂ => env_regs h₁.env h₂.env) (fun s₁ s₂ h₁ h₂ => by rw [h₁.env.sp, h₂.env.sp])
    (fun s h => ⟨by rw [h.env.sp]; have := h.afit; omega, fun r hr => by
      rw [h.env.sp]; exact (h.wa r hr).sub_left (Region.sub_prefix (by decide))⟩)
    (fun s₁ s₂ h₁ h₂ => argMem_of (by rw [h₁.env.sp, h₂.env.sp]) (by rw [h₁.env.sp]; have := h₁.afit; omega)
      fun i hi => by
        rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
        · rw [h₁.arg.1, h₂.arg.1]
        · rw [h₁.arg.2, h₂.arg.2]) hA

omit hR in
theorem cmpLoad_wp {D : BitVec 32} {n : Nat} {s : State} (h : CtrI c w sp R D n s) :
    WP isa (.block (compare ++ ([.ldrSp .r6 0, .ldrSp .r5 4] : List Instr))) s fun s' =>
      (CtrI c w sp R D n s' ∧ s'.gpr .r6 = D ∧ s'.gpr .r5 = BitVec.ofNat 32 n) ∧
        ∃ ok : Bool, s'.gpr .r0 = if ok then 1 else 0 := by
  obtain ⟨s₁, run, h0, g, k⟩ := compare_ok L h.env
  refine WP.block_append_iff.mpr (WP.of_runBlock ⟨s₁, run, ?_⟩)
  have he : Env c w sp R s₁ := h.env.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact g _ (by decide) (by decide) (by decide)) k.sp k.rd k.wr
  have h₁ : CtrI c w sp R D n s₁ := h.next he k.rd k.wr (rs := []) (by rw [k.mem]; exact Frame.refl _ _)
    (fun _ hr => by simp at hr)
  refine WP.mono (loadArgs_wp h₁) fun s' ⟨p, e0⟩ => ⟨p, decide (bytesAt s.mem (State.addr w + BitVec.ofNat 64 0) 16 =
    bytesAt s.mem (State.addr w + BitVec.ofNat 64 tOff) 16), ?_⟩
  rw [e0, h0]; simp only [decide_eq_true_eq]

omit L hR in
/-- The data masked with `0 − r0`. -/
theorem maskData_ct {D : BitVec 32} {n : Nat} :
    CT (fun s => CtrI c w sp R D n s ∧ s.gpr .r6 = D ∧ s.gpr .r5 = BitVec.ofNat 32 n) maskData := by
  obtain ⟨_, hA⟩ : ∃ h, (Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs [.r5, .r6]) maskData h).isSome = true :=
    ⟨_, by taint_decide⟩
  exact CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.2.2, h₂.2.2]
    · rw [h₁.2.1, h₂.2.1]) hA

/-- `vg_aes_siv_encrypt`, in two runs with the same public arguments and
descriptors, with `siv` writable. -/
theorem encrypt_ct {a D T : BitVec 32} {N n : Nat} {dsc : Nat → Nat → BitVec 32} (hN : N < 2 ^ 32)
    (hn : n < 2 ^ 32) :
    CT (fun s => E0 c w sp a D T R N n dsc s ∧ Covers [⟨State.addr T, 16⟩] s.wr) encrypt := by
  refine CT.seq ((encS2v_ct L hR hN).mono fun s h => h.1) (J := fun s =>
      (CtrI c w sp R D n s ∧ s.gpr .r6 = D ∧ s.gpr .r5 = BitVec.ofNat 32 n) ∧ SivA w sp T s ∧
        Covers [⟨State.addr T, 16⟩] s.wr)
    (fun s h => WP.mono (encS2v_wp L h.1) fun s' ⟨p, q, e⟩ => ⟨p, q, by rw [e]; exact h.2⟩) ?_
  refine CT.seq (J := fun s => CtrI c w sp R D n s ∧ SivA w sp T s ∧ Covers [⟨State.addr T, 16⟩] s.wr)
    ((finish_ct L hR hn (.inl rfl)).mono fun s h => ⟨h.1.1.env, h.1.1.dat.buf, h.1.2.1, h.1.2.2⟩)
    (fun s h => WP.mono (finish_ok L h.1.1.env hR h.1.1.dat.buf h.1.1.n32 h.1.2.1 h.1.2.2 (.inl rfl))
      fun s' ⟨he, rd, wr, _, f, _⟩ => ⟨h.1.1.next he rd wr f (args_dis_oR h.1.1.args_w (.inl rfl)),
        h.2.1.next rd wr f (args_dis_oR h.1.1.args_w (.inl rfl)), by rw [wr]; exact h.2.2⟩) ?_
  refine CT.seq (J := fun s => CtrI c w sp R D n s ∧ SivA w sp T s ∧ Covers [⟨State.addr T, 16⟩] s.wr)
    ((ctr_ct L hR hn).mono fun s h => h.1)
    (fun s h => WP.mono (ctr_ok L h.1.env hR h.1.dat hn h.1.afit h.1.args h.1.args_w h.1.m0 h.1.m1)
      fun s' ⟨he, rd, wr, _, _, _, f, _⟩ => ⟨h.1.next he rd wr f (args_dis_ctr h.1.args_w h.1.args_d),
        h.2.1.next rd wr f (args_dis_ctr h.1.args_w h.1.args_d), by rw [wr]; exact h.2.2⟩) ?_
  exact CT.seq (J := Env c w sp R) sivOut_ct (fun s h => sivOut_wp L h) restore_ct

/-- `vg_aes_siv_decrypt`, in two runs with the same public arguments and descriptors. -/
theorem decrypt_ct {a D T : BitVec 32} {N n : Nat} {dsc : Nat → Nat → BitVec 32} (hN : N < 2 ^ 32)
    (hn : n < 2 ^ 32) : CT (E0 c w sp a D T R N n dsc) decrypt := by
  refine CT.seq (encS2v_ct L hR hN) (J := fun s => CtrI c w sp R D n s ∧ SivA w sp T s)
    (fun s h => WP.mono (encS2v_wp L h) fun s' ⟨p, q, _⟩ => ⟨p.1, q⟩) ?_
  refine CT.seq sivIn_ct (fun s h => sivIn_wp L h) ?_
  refine CT.seq (J := CtrI c w sp R D n) (ctr_ct L hR hn)
    (fun s h => WP.mono (ctr_ok L h.env hR h.dat hn h.afit h.args h.args_w h.m0 h.m1)
      fun s' ⟨he, rd, wr, _, _, _, f, _⟩ => h.next he rd wr f (args_dis_ctr h.args_w h.args_d)) ?_
  refine CT.seq loadArgs_ct (fun s h => WP.mono (loadArgs_wp h) fun s' p => p.1) ?_
  refine CT.seq (J := CtrI c w sp R D n) ((finish_ct L hR hn (.inr rfl)).mono
      fun s h => ⟨h.1.env, h.1.dat.buf, h.2.1, h.2.2⟩)
    (fun s h => finish_next L hR (.inr rfl) h (args_dis_oR h.1.args_w (.inr rfl))) ?_
  refine CT.seq cmpLoad_ct (fun s h => cmpLoad_wp L h) ?_
  exact CT.seq (J := Env c w sp R) (maskData_ct.mono fun s h => h.1)
    (fun s ⟨⟨h, h6, h5⟩, ok, h0⟩ => WP.mono (maskData_ok h.env h.dat hn h6 h5 h0) fun s' p => p.1) restore_ct

end

end VG.Proof.AesSiv.Arm
