import VerifiedGarbage.Proof.MlDsa.Arm.Arith.AddSub
import VerifiedGarbage.Proof.MlKem.Arm.CallF
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Impl.MlDsa.Arm.Arith.Common
import VerifiedGarbage.Impl.MlDsa.Arm.Arith.Mul

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Arith.Saving`. -/
section

/-!
# ML-DSA on 32-bit ARM: registers saved in frames

`saving rs body` pushes each register of `rs` in a frame of its own, runs
`body`, and restores each with the pop of its frame. If `body` writes memory
only in regions `W` that do not overlap the `4 · |rs|` bytes below the stack
pointer, the frames hold the registers until they are popped (`wp_saving`):
the registers `rs` are restored, the others are what `body` left, and so are
memory and `rd`, while `sp` and `wr` are back as on entry. `body` runs from a
state with the same registers and `rd`, more writable regions (the frames, at
the head of `wr`), and memory changed only below the stack pointer (`Entry`).

`ct_saving`: the push and pop of a frame leak only addresses computed from
the stack pointer, so `saving rs body` is constant time if `body` is, by the
taint analysis, from the registers `ps` public.
-/

namespace VG.Proof.MlDsa.Arm.Arith

open VG VG.Arm VG.Impl.MlDsa.Arm.Arith

/-- What the state `s₁` in which `body` starts keeps of the state `s` on
entry to `saving rs body`. -/
structure Entry (n : Nat) (s s₁ : VG.Arm.State) : Prop where
  gpr : s₁.gpr = s.gpr
  rd : s₁.rd = s.rd
  wr : ∀ R ∈ s.wr, R ∈ s₁.wr
  frame : Frame [belowA s.sp n] s.mem s₁.mem

theorem entry_refl (s : VG.Arm.State) : VG.Proof.MlDsa.Arm.Arith.Entry 0 s s :=
  ⟨rfl, rfl, fun _ h => h, Frame.refl _ _⟩

/-- The word at `sp - 4` of the push of `r`. -/
theorem pushed_word (r : Reg) (s : VG.Arm.State) :
    (pushed [r] s).mem.readW (State.addr (s.sp - 4)) 32 = s.gpr r :=
  Mem.readW_writeW_self32 _ _ _

theorem word_region (sp : BitVec 32) {n : Nat} (h : 4 + n ≤ sp.toNat) :
    (belowA sp (4 + n)).Contains (State.addr (sp - 4)) 4 := by
  have := addr_toNat' sp
  have := addr_toNat' (sp - 4)
  simp only [belowA, Region.Contains]
  bv_omega

theorem word_disj (sp : BitVec 32) {n : Nat} (h : 4 + n ≤ sp.toNat) :
    (⟨State.addr (sp - 4), 4⟩ : Region).Disjoint (belowA (sp - 4) n) := by
  intro x hx hy
  have := addr_toNat' sp
  have := addr_toNat' (sp - 4)
  simp only [belowA, Region.Contains] at hx hy
  bv_omega

theorem wp_saving (rs : List Reg) (body : Prog isa) {W : List Region} :
    ∀ (Q : VG.Arm.State → Prop) (s : VG.Arm.State), 4 * rs.length ≤ s.sp.toNat → (∀ R ∈ W, (belowA s.sp (4 * rs.length)).Disjoint R) →
    (∀ s₁, VG.Proof.MlDsa.Arm.Arith.Entry (4 * rs.length) s s₁ → WP isa body s₁ fun s₂ => Frame W s₁.mem s₂.mem ∧ Q s₂) →
    WP isa (saving rs body) s fun s' => ∃ s₂, Q s₂ ∧ s'.mem = s₂.mem ∧ s'.rd = s₂.rd ∧
      s'.sp = s.sp ∧ s'.wr = s.wr ∧ ∀ r, s'.gpr r = if r ∈ rs then s.gpr r else s₂.gpr r := by
  induction rs with
  | nil =>
    intro Q s _ _ hb
    obtain ⟨t, s₂, he, -, hq⟩ := hb s (VG.Proof.MlDsa.Arm.Arith.entry_refl s)
    obtain ⟨-, hw, hsp⟩ := Exec.rdwr he
    exact ⟨t, s₂, he, s₂, hq, rfl, rfl, hsp, hw, fun r => by simp⟩
  | cons r rs ih =>
    intro Q s hsp hW hb
    simp only [List.length_cons, Nat.mul_add, Nat.mul_one] at hsp hW hb
    have hs4 : 4 ≤ s.sp.toNat := by omega
    have e4 : (4 : BitVec 32) = BitVec.ofNat 32 (4 * [r].length) := rfl
    have hsp' : (s.sp - 4).toNat = s.sp.toNat - 4 := by bv_omega
    have hsub : Region.Sub (belowA (s.sp - 4) (4 * rs.length)) (belowA s.sp (4 * rs.length + 4)) := by
      have := belowA_push (sp := s.sp) (k := 4) (a := 4 * rs.length) (by omega)
      rwa [Nat.add_comm] at this
    have hwd := VG.Proof.MlDsa.Arm.Arith.word_region s.sp (n := 4 * rs.length) (by omega)
    rw [Nat.add_comm] at hwd
    refine WP.frame (rs := [r]) (r := r) rfl (by simp; omega) (by simp) ?_
    have ih' := ih (fun s₂ => Q s₂ ∧ s₂.mem.readW (State.addr (s.sp - 4)) 32 = s.gpr r) (pushed [r] s)
      (by rw [pushed_sp, ← e4, hsp']; omega)
      (fun R hR => (hW R hR).sub_left (by rw [pushed_sp, ← e4]; exact hsub)) (fun s₁ hE => ?_)
    · refine WP.mono ih' fun s' ⟨s₂, ⟨hq, hword⟩, hm, hrd, hsp₂, hwr, hg⟩ => ⟨s₂, hq, ?_, ?_, ?_, ?_, ?_⟩
      · exact hm
      · exact hrd
      · simp only [popped_sp, hsp₂, pushed_sp]; rw [← e4]; exact BitVec.sub_add_cancel _ _
      · simp only [popped_wr, hwr, pushed_wr, List.tail_cons]
      · intro r'
        by_cases e : r' = r
        · subst e
          simp only [popped, State.setReg, ite_true, List.mem_cons, true_or]
          rw [hm, hsp₂, pushed_sp, ← e4]; exact hword
        · rw [popped_gpr e, hg r', pushed_gpr]
          simp only [List.mem_cons, e, false_or]
    · -- The body, from the state after all the pushes.
      have hE' : VG.Proof.MlDsa.Arm.Arith.Entry (4 * rs.length + 4) s s₁ := by
        refine ⟨hE.gpr.trans (pushed_gpr _ _), hE.rd.trans (pushed_rd _ _),
          fun R hR => hE.wr R (by rw [pushed_wr]; exact List.mem_cons_of_mem _ hR), ?_⟩
        have f₀ : Frame [⟨State.addr (s.sp - 4), 4⟩] s.mem (pushed [r] s).mem := by
          have := storeWords_frame s.mem (s.sp - BitVec.ofNat 32 (4 * [r].length)) [s.gpr r]
            (by simp; bv_omega)
          simp only [List.length_singleton] at this
          exact this
        refine (f₀.sub fun R hR => ?_).trans (hE.frame.sub fun R hR => ?_)
        · rw [List.mem_singleton] at hR; subst hR
          refine ⟨_, List.mem_singleton_self _, fun x hx => hwd.byte ?_⟩
          simp only [Region.Contains] at hx ⊢
          omega
        · rw [List.mem_singleton] at hR; subst hR
          refine ⟨_, List.mem_singleton_self _, ?_⟩
          rw [pushed_sp, ← e4]; exact hsub
      refine WP.mono (hb s₁ hE') fun s₂ ⟨hf, hq⟩ => ⟨hf, hq, ?_⟩
      have hw₁ : s₁.mem.readW (State.addr (s.sp - 4)) 32 = s.gpr r := by
        rw [hE.frame.readW (r := ⟨State.addr (s.sp - 4), 4⟩) (Region.contains_self _ _)
          (fun R hR => by
            rw [List.mem_singleton] at hR; subst hR
            rw [pushed_sp, ← e4]; exact VG.Proof.MlDsa.Arm.Arith.word_disj s.sp (by omega)) (by decide)]
        exact VG.Proof.MlDsa.Arm.Arith.pushed_word r s
      rw [hf.readW (r := belowA s.sp (4 * rs.length + 4)) hwd (fun R hR => hW R hR) (by decide), hw₁]

/-- `saving rs body` is constant time if the taint analysis proves `body`
constant time from the registers `ps` public. -/
theorem ct_saving (rs : List Reg) (body : Prog isa) (ps : List Reg) {hc : VG.Taint.Hint VG.Arm.taint.T}
    (h : (VG.Arm.taint.check (Taint.ofRegs ps) body hc).isSome = true) :
    ∀ P : VG.Arm.State → VG.Arm.State → Prop, (∀ s₁ s₂, P s₁ s₂ → s₁.sp = s₂.sp ∧ ∀ r ∈ ps, s₁.gpr r = s₂.gpr r) →
      RelCT isa P (saving rs body) fun _ _ => True := by
  induction rs with
  | nil =>
    intro P hP
    exact RelCT.taint (A := VG.Arm.taint) (Taint.ofRegs ps)
      (fun s₁ s₂ hp => Taint.agree_ofRegs (hP s₁ s₂ hp).2) h
  | cons r rs ih =>
    intro P hP
    refine RelCT.frame (fun s₁ s₂ hp => (hP s₁ s₂ hp).1) (ih _ fun a b ⟨s₁, s₂, hp, h₁, h₂⟩ => ?_)
    obtain ⟨rfl, -⟩ := push_pushed' h₁
    obtain ⟨rfl, -⟩ := push_pushed' h₂
    obtain ⟨hsp, hg⟩ := hP s₁ s₂ hp
    exact ⟨by rw [pushed_sp, pushed_sp, hsp], fun r hr => by rw [pushed_gpr, pushed_gpr]; exact hg r hr⟩


/-- Constant time of `saving rs body` for a contract whose public data
include the stack pointer and the registers `ps`. -/
theorem ct_of_saving {k : Contract isa} (rs : List Reg) (body : Prog isa) (ps : List Reg)
    (hpub : ∀ s₁ s₂, k.pub s₁ s₂ → s₁.sp = s₂.sp ∧ ∀ r ∈ ps, s₁.gpr r = s₂.gpr r)
    {hc : VG.Taint.Hint VG.Arm.taint.T} (h : (VG.Arm.taint.check (Taint.ofRegs ps) body hc).isSome = true) :
    ConstantTime isa k.pre k.pub (saving rs body) :=
  RelCT.constantTime (VG.Proof.MlDsa.Arm.Arith.ct_saving rs body ps h _ fun s₁ s₂ hp => hpub s₁ s₂ hp.2.2)

/-- The callee-saved registers after `saving rs body`, if `rs` and the
registers `body` keeps cover them. -/
theorem preserved_of_saving {rs : List Reg} {s s' s₂ : VG.Arm.State}
    (hg : ∀ r, s'.gpr r = if r ∈ rs then s.gpr r else s₂.gpr r)
    (hk : ∀ r ∈ preserved, r ∉ rs → s₂.gpr r = s.gpr r) : ∀ r ∈ preserved, s'.gpr r = s.gpr r := by
  intro r hr
  rw [hg r]
  split
  · rfl
  · exact hk r hr ‹_›

end VG.Proof.MlDsa.Arm.Arith

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Arith.Mul`. -/
section

/-!
# ML-DSA on 32-bit ARM: `vg_mldsa_multiply_ntt` and `vg_mldsa_multiply_add_ntt`

The loop body is three blocks, each symbolically executed once for any state:
the loads and the zPieces (`head_ok`), `mulz` (`mulz_ok`) and the rest
(`tail_ok`, `tailAdd_ok`); the loop invariant says which coefficients of `h`
are done (`Inv`), and `wp_saving` puts the loop in the frames that save
`r4`–`r9`.
-/

namespace VG.Proof.MlDsa.Arm.Arith.Mul

open VG VG.Arm VG.Impl.MlDsa.Arm.Arith
open VG.Spec.MlDsa
open VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.Arm (wp_loop_ne count_z count_sub addr_ptr inRegions_of)
open VG.Proof.MlDsa.Arm.Arith.AddSub (ptr_succ reduced_zero ctRegs)

/-! ## The loop body -/

/-- The registers the body does not write, of those it must preserve. -/
def Keep (s s' : State) : Prop := s'.gpr .r10 = s.gpr .r10 ∧ s'.gpr .r11 = s.gpr .r11 ∧ s'.gpr .lr = s.gpr .lr

theorem Keep.trans {s₁ s₂ s₃ : State} (h₁ : VG.Proof.MlDsa.Arm.Arith.Mul.Keep s₁ s₂) (h₂ : VG.Proof.MlDsa.Arm.Arith.Mul.Keep s₂ s₃) : VG.Proof.MlDsa.Arm.Arith.Mul.Keep s₁ s₃ :=
  ⟨h₂.1.trans h₁.1, h₂.2.1.trans h₁.2.1, h₂.2.2.trans h₁.2.2⟩

theorem head_ok {s : State} {y w : BitVec 32} (h1 : s.gpr .r1 = y) (h2 : s.gpr .r2 = w)
    (iF : InRegions (s.rd ++ s.wr) (State.addr (y + BitVec.ofNat 32 0)) 4)
    (iG : InRegions (s.rd ++ s.wr) (State.addr (w + BitVec.ofNat 32 0)) 4) :
    WP isa (.block (([.ldr .r12 .r1 0] : List Instr) ++ zPieces .r12 ++ ([.ldr .r8 .r2 0] : List Instr))) s fun s' =>
      s'.gpr .r5 = s.mem.readW (State.addr (y + BitVec.ofNat 32 0)) 32 >>> 14 ∧
      s'.gpr .r6 = s.mem.readW (State.addr (y + BitVec.ofNat 32 0)) 32 <<< 18 >>> 25 ∧
      s'.gpr .r7 = s.mem.readW (State.addr (y + BitVec.ofNat 32 0)) 32 <<< 25 >>> 25 ∧
      s'.gpr .r8 = s.mem.readW (State.addr (w + BitVec.ofNat 32 0)) 32 ∧
      (∀ r, r ≠ .r5 → r ≠ .r6 → r ≠ .r7 → r ≠ .r8 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  run_block [zPieces, h1, h2, iF, iG]
  and_intros
  all_goals first | trivial | (intro r h5 h6 h7 h8 h12; simp [h5, h6, h7, h8, h12])

/-- What the rest of an iteration does, but for the value stored. -/
def Step (s : State) (x y w c v : BitVec 32) (s' : State) : Prop :=
  s'.gpr .r0 = x + 4 ∧ s'.gpr .r1 = y + 4 ∧ s'.gpr .r2 = w + 4 ∧ s'.gpr .r3 = c - 1 ∧ s'.z = (c - 1 == 0) ∧
    s'.gpr .r4 = Qw ∧ VG.Proof.MlDsa.Arm.Arith.Mul.Keep s s' ∧
    s'.mem = s.mem.writeW (State.addr (x + BitVec.ofNat 32 0)) v ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp

section
variable {s : State} {x y w c p : BitVec 32} (h0 : s.gpr .r0 = x) (h1 : s.gpr .r1 = y) (h2 : s.gpr .r2 = w)
  (h3 : s.gpr .r3 = c) (h4 : s.gpr .r4 = Qw) (h9 : s.gpr .r9 = p)
  (oH : InRegions s.wr (State.addr (x + BitVec.ofNat 32 0)) 4)
include h0 h1 h2 h3 h4 h9 oH

theorem tail_ok :
    WP isa (.block (csub .r9 .r12 .r4 ++ ([.str .r9 .r0 0] : List Instr) ++ step3)) s (VG.Proof.MlDsa.Arm.Arith.Mul.Step s x y w c (bcsub p)) := by
  run_block [csub, VG.Impl.MlDsa.Arm.Arith.fixup, step3, VG.Proof.MlDsa.Arm.Arith.Mul.Step, VG.Proof.MlDsa.Arm.Arith.Mul.Keep, bcsub, bfix, h0, h1, h2, h3, h4, h9, oH]

theorem tailAdd_ok (iH : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 0)) 4) :
    WP isa (.block (([.ldr .r8 .r0 0, .dp .add .r9 .r9 (.reg .r8)] : List Instr) ++ red .r9 .r12 .r4 ++
      csub .r9 .r12 .r4 ++ ([.str .r9 .r0 0] : List Instr) ++ step3)) s
      (VG.Proof.MlDsa.Arm.Arith.Mul.Step s x y w c (bcsub (bred (p + s.mem.readW (State.addr (x + BitVec.ofNat 32 0)) 32)))) := by
  run_block [red, csub, VG.Impl.MlDsa.Arm.Arith.fixup, step3, VG.Proof.MlDsa.Arm.Arith.Mul.Step, VG.Proof.MlDsa.Arm.Arith.Mul.Keep, bcsub, bfix, bred, h0, h1, h2, h3, h4, h9, oH, iH]

end

/-- The product of the coefficients at `y` and `w`, as `mulHead` leaves it. -/
abbrev prod (m : Mem) (y w : BitVec 32) : BitVec 32 :=
  let a := m.readW (State.addr (y + BitVec.ofNat 32 0)) 32
  bmulz (m.readW (State.addr (w + BitVec.ofNat 32 0)) 32) (a >>> 14) (a <<< 18 >>> 25) (a <<< 25 >>> 25)

section
variable {s : State} {x y w c : BitVec 32} (h0 : s.gpr .r0 = x) (h1 : s.gpr .r1 = y) (h2 : s.gpr .r2 = w)
  (h3 : s.gpr .r3 = c) (h4 : s.gpr .r4 = Qw)
  (iF : InRegions (s.rd ++ s.wr) (State.addr (y + BitVec.ofNat 32 0)) 4)
  (iG : InRegions (s.rd ++ s.wr) (State.addr (w + BitVec.ofNat 32 0)) 4)
  (oH : InRegions s.wr (State.addr (x + BitVec.ofNat 32 0)) 4)
include h0 h1 h2 h3 h4 iF iG oH

omit oH in
/-- The head and `mulz`, and then `k`. -/
theorem headMul {Q : State → Prop}
    (k : ∀ s', s'.gpr .r0 = x → s'.gpr .r1 = y → s'.gpr .r2 = w → s'.gpr .r3 = c → s'.gpr .r4 = Qw →
      s'.gpr .r9 = VG.Proof.MlDsa.Arm.Arith.Mul.prod s.mem y w → VG.Proof.MlDsa.Arm.Arith.Mul.Keep s s' → s'.mem = s.mem →
      s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → Q s') :
    WP isa (.block (mulHead ++ [])) s Q := by
  rw [List.append_nil, mulHead, WP.block_append_iff]
  refine WP.mono (VG.Proof.MlDsa.Arm.Arith.Mul.head_ok h1 h2 iF iG) fun s₁ ⟨e5, e6, e7, e8, eo, m₁, rd₁, wr₁, sp₁⟩ => ?_
  refine WP.mono (mulz_ok (by rw [eo _ (by decide) (by decide) (by decide) (by decide) (by decide), h4]) e5 e6 e7 e8)
    fun s₂ ⟨e9, eo₂, m₂, rd₂, wr₂, sp₂⟩ => ?_
  have g : ∀ r, r ≠ .r5 → r ≠ .r6 → r ≠ .r7 → r ≠ .r8 → r ≠ .r9 → r ≠ .r12 → s₂.gpr r = s.gpr r :=
    fun r a5 a6 a7 a8 a9 a12 => (eo₂ r a9 a12).trans (eo r a5 a6 a7 a8 a12)
  refine k s₂ ((g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h0)
    ((g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h1)
    ((g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h2)
    ((g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h3)
    ((g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h4)
    e9 ⟨g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)⟩
    (m₂.trans m₁) (rd₂.trans rd₁) (wr₂.trans wr₁) (sp₂.trans sp₁)

theorem body_ok : WP isa (.block mulBody) s (VG.Proof.MlDsa.Arm.Arith.Mul.Step s x y w c (bcsub (VG.Proof.MlDsa.Arm.Arith.Mul.prod s.mem y w))) := by
  rw [mulBody, List.append_assoc, List.append_assoc, WP.block_append_iff, ← List.append_nil mulHead]
  refine VG.Proof.MlDsa.Arm.Arith.Mul.headMul h0 h1 h2 h3 h4 iF iG fun s₂ e0 e1 e2 e3 e4 e9 eo m rd wr sp => ?_
  rw [← List.append_assoc]
  have iH' : InRegions s₂.wr (State.addr (x + BitVec.ofNat 32 0)) 4 := by rw [wr]; exact oH
  refine WP.mono (VG.Proof.MlDsa.Arm.Arith.Mul.tail_ok e0 e1 e2 e3 e4 e9 iH') fun s' ⟨r0, r1, r2, r3, z, r4, ro, m', rd', wr', sp'⟩ =>
    ⟨r0, r1, r2, r3, z, r4, eo.trans ro, by rw [m', m], rd'.trans rd, wr'.trans wr,
      sp'.trans sp⟩

theorem bodyAdd_ok (iH : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 0)) 4) :
    WP isa (.block mulAddBody) s (VG.Proof.MlDsa.Arm.Arith.Mul.Step s x y w c
      (bcsub (bred (VG.Proof.MlDsa.Arm.Arith.Mul.prod s.mem y w + s.mem.readW (State.addr (x + BitVec.ofNat 32 0)) 32)))) := by
  rw [mulAddBody, List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc,
    WP.block_append_iff, ← List.append_nil mulHead]
  refine VG.Proof.MlDsa.Arm.Arith.Mul.headMul h0 h1 h2 h3 h4 iF iG fun s₂ e0 e1 e2 e3 e4 e9 eo m rd wr sp => ?_
  simp only [← List.append_assoc]
  have iH' : InRegions s₂.wr (State.addr (x + BitVec.ofNat 32 0)) 4 := by rw [wr]; exact oH
  have iH'' : InRegions (s₂.rd ++ s₂.wr) (State.addr (x + BitVec.ofNat 32 0)) 4 := by rw [wr, rd]; exact iH
  refine WP.mono (VG.Proof.MlDsa.Arm.Arith.Mul.tailAdd_ok e0 e1 e2 e3 e4 e9 iH' iH'')
    fun s' ⟨r0, r1, r2, r3, z, r4, ro, m', rd', wr', sp'⟩ =>
    ⟨r0, r1, r2, r3, z, r4, eo.trans ro, by rw [m', m], rd'.trans rd, wr'.trans wr,
      sp'.trans sp⟩

end

/-! ## The loop -/

section
variable (s₀ : State)

abbrev ph : BitVec 32 := s₀.gpr .r0
abbrev pf : BitVec 32 := s₀.gpr .r1
abbrev pg : BitVec 32 := s₀.gpr .r2
abbrev H : Addr := State.addr (VG.Proof.MlDsa.Arm.Arith.Mul.ph s₀)
abbrev F : Addr := State.addr (VG.Proof.MlDsa.Arm.Arith.Mul.pf s₀)
abbrev G : Addr := State.addr (VG.Proof.MlDsa.Arm.Arith.Mul.pg s₀)

end

/-- What the body's loop needs of the state it starts in. -/
structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [polyRegion (VG.Proof.MlDsa.Arm.Arith.Mul.F s₀), polyRegion (VG.Proof.MlDsa.Arm.Arith.Mul.G s₀)]
  wr : polyRegion (VG.Proof.MlDsa.Arm.Arith.Mul.H s₀) ∈ s₀.wr
  hf : (polyRegion (VG.Proof.MlDsa.Arm.Arith.Mul.H s₀)).Disjoint (polyRegion (VG.Proof.MlDsa.Arm.Arith.Mul.F s₀))
  hg : (polyRegion (VG.Proof.MlDsa.Arm.Arith.Mul.H s₀)).Disjoint (polyRegion (VG.Proof.MlDsa.Arm.Arith.Mul.G s₀))
  fitH : (VG.Proof.MlDsa.Arm.Arith.Mul.ph s₀).toNat + 1024 ≤ 2 ^ 32
  fitF : (VG.Proof.MlDsa.Arm.Arith.Mul.pf s₀).toNat + 1024 ≤ 2 ^ 32
  fitG : (VG.Proof.MlDsa.Arm.Arith.Mul.pg s₀).toNat + 1024 ≤ 2 ^ 32
  redF : Reduced s₀.mem (VG.Proof.MlDsa.Arm.Arith.Mul.F s₀)
  redG : Reduced s₀.mem (VG.Proof.MlDsa.Arm.Arith.Mul.G s₀)

/-- After `i` iterations, writing `out j` to coefficient `j` of `h`. -/
structure Inv (out : Nat → BitVec 32) (s₀ : State) (i : Nat) (s : State) : Prop where
  r0 : s.gpr .r0 = VG.Proof.MlDsa.Arm.Arith.Mul.ph s₀ + BitVec.ofNat 32 (4 * i)
  r1 : s.gpr .r1 = VG.Proof.MlDsa.Arm.Arith.Mul.pf s₀ + BitVec.ofNat 32 (4 * i)
  r2 : s.gpr .r2 = VG.Proof.MlDsa.Arm.Arith.Mul.pg s₀ + BitVec.ofNat 32 (4 * i)
  r3 : s.gpr .r3 = BitVec.ofNat 32 (1 * (256 - i))
  r4 : s.gpr .r4 = Qw
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  keep : VG.Proof.MlDsa.Arm.Arith.Mul.Keep s₀ s
  frame : Frame [polyRegion (VG.Proof.MlDsa.Arm.Arith.Mul.H s₀)] s₀.mem s.mem
  coeff : ∀ j < 256, coeffAt s.mem (VG.Proof.MlDsa.Arm.Arith.Mul.H s₀) j = if j < i then out j else coeffAt s₀.mem (VG.Proof.MlDsa.Arm.Arith.Mul.H s₀) j

/-- The facts about memory an iteration needs. -/
structure Acc (s₀ : State) (i : Nat) (s : State) : Prop where
  iF : InRegions (s.rd ++ s.wr) (State.addr (VG.Proof.MlDsa.Arm.Arith.Mul.pf s₀ + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 0)) 4
  iG : InRegions (s.rd ++ s.wr) (State.addr (VG.Proof.MlDsa.Arm.Arith.Mul.pg s₀ + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 0)) 4
  iH : InRegions (s.rd ++ s.wr) (State.addr (VG.Proof.MlDsa.Arm.Arith.Mul.ph s₀ + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 0)) 4
  oH : InRegions s.wr (State.addr (VG.Proof.MlDsa.Arm.Arith.Mul.ph s₀ + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 0)) 4
  vF : s.mem.readW (State.addr (VG.Proof.MlDsa.Arm.Arith.Mul.pf s₀ + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 0)) 32 = coeffAt s₀.mem (VG.Proof.MlDsa.Arm.Arith.Mul.F s₀) i
  vG : s.mem.readW (State.addr (VG.Proof.MlDsa.Arm.Arith.Mul.pg s₀ + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 0)) 32 = coeffAt s₀.mem (VG.Proof.MlDsa.Arm.Arith.Mul.G s₀) i
  vH : s.mem.readW (State.addr (VG.Proof.MlDsa.Arm.Arith.Mul.ph s₀ + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 0)) 32 = coeffAt s₀.mem (VG.Proof.MlDsa.Arm.Arith.Mul.H s₀) i

theorem acc_of {out : Nat → BitVec 32} {s₀ : State} (hp : VG.Proof.MlDsa.Arm.Arith.Mul.Pre s₀) {i : Nat} (hi : i < 256) {s : State}
    (h : VG.Proof.MlDsa.Arm.Arith.Mul.Inv out s₀ i s) : VG.Proof.MlDsa.Arm.Arith.Mul.Acc s₀ i s := by
  have fF := hp.fitF
  have fG := hp.fitG
  have fH := hp.fitH
  have eF : State.addr (VG.Proof.MlDsa.Arm.Arith.Mul.pf s₀ + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 0) = coeffAddr (VG.Proof.MlDsa.Arm.Arith.Mul.F s₀) i :=
    addr_ptr _ _ _ (by omega)
  have eG : State.addr (VG.Proof.MlDsa.Arm.Arith.Mul.pg s₀ + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 0) = coeffAddr (VG.Proof.MlDsa.Arm.Arith.Mul.G s₀) i :=
    addr_ptr _ _ _ (by omega)
  have eH : State.addr (VG.Proof.MlDsa.Arm.Arith.Mul.ph s₀ + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 0) = coeffAddr (VG.Proof.MlDsa.Arm.Arith.Mul.H s₀) i :=
    addr_ptr _ _ _ (by omega)
  have cF := coeff_contains (VG.Proof.MlDsa.Arm.Arith.Mul.F s₀) (i := i) hi
  have cG := coeff_contains (VG.Proof.MlDsa.Arm.Arith.Mul.G s₀) (i := i) hi
  have cH := coeff_contains (VG.Proof.MlDsa.Arm.Arith.Mul.H s₀) (i := i) hi
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [eF, h.rd, h.wr, hp.rd]; exact inRegions_of (by simp) cF
  · rw [eG, h.rd, h.wr, hp.rd]; exact inRegions_of (by simp) cG
  · rw [eH, h.rd, h.wr]; exact inRegions_of (List.mem_append_right _ hp.wr) cH
  · rw [eH, h.wr]; exact inRegions_of hp.wr cH
  · rw [eF, ← coeffAt_eq]
    exact coeffAt_frame h.frame (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hp.hf.symm) hi
  · rw [eG, ← coeffAt_eq]
    exact coeffAt_frame h.frame (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hp.hg.symm) hi
  · rw [eH, ← coeffAt_eq, h.coeff i hi, ite_eq_right (Nat.lt_irrefl i)]

/-- One iteration, from the value the body stores. -/
theorem inv_step {out : Nat → BitVec 32} {s₀ : State} (hp : VG.Proof.MlDsa.Arm.Arith.Mul.Pre s₀) {i : Nat} (hi : i < 256)
    {s : State} (h : VG.Proof.MlDsa.Arm.Arith.Mul.Inv out s₀ i s) {body : List Instr}
    (hb : WP isa (.block body) s (VG.Proof.MlDsa.Arm.Arith.Mul.Step s (VG.Proof.MlDsa.Arm.Arith.Mul.ph s₀ + BitVec.ofNat 32 (4 * i)) (VG.Proof.MlDsa.Arm.Arith.Mul.pf s₀ + BitVec.ofNat 32 (4 * i))
      (VG.Proof.MlDsa.Arm.Arith.Mul.pg s₀ + BitVec.ofNat 32 (4 * i)) (BitVec.ofNat 32 (1 * (256 - i))) (out i))) :
    WP isa (.block body) s fun s' => VG.Proof.MlDsa.Arm.Arith.Mul.Inv out s₀ (i + 1) s' ∧ s'.z = decide (i + 1 = 256) := by
  have fH := hp.fitH
  have eH : State.addr (VG.Proof.MlDsa.Arm.Arith.Mul.ph s₀ + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 0) = coeffAddr (VG.Proof.MlDsa.Arm.Arith.Mul.H s₀) i :=
    addr_ptr _ _ _ (by omega)
  have cH := coeff_contains (VG.Proof.MlDsa.Arm.Arith.Mul.H s₀) (i := i) hi
  refine WP.mono hb fun s' ⟨r0, r1, r2, r3, z, r4, ro, m, rd, wr, sp⟩ => ⟨⟨?_, ?_, ?_, ?_, r4,
    rd.trans h.rd, wr.trans h.wr, sp.trans h.sp, h.keep.trans ro, ?_, ?_⟩, ?_⟩
  · rw [r0]; exact VG.Proof.MlDsa.Arm.Arith.AddSub.ptr_succ _ 4 i
  · rw [r1]; exact VG.Proof.MlDsa.Arm.Arith.AddSub.ptr_succ _ 4 i
  · rw [r2]; exact VG.Proof.MlDsa.Arm.Arith.AddSub.ptr_succ _ 4 i
  · rw [r3]; exact count_sub (k := 1) hi
  · rw [m, eH]
    exact h.frame.writeW (List.mem_singleton_self _) _ cH
  · intro j hj
    rw [m, eH, coeffAt_writeW _ _ hj hi, h.coeff j hj]
    by_cases hij : i = j
    · subst hij; simp
    · rw [ite_eq_right hij]
      by_cases hj' : j < i
      · rw [ite_eq_left hj', ite_eq_left (by omega)]
      · rw [ite_eq_right hj', ite_eq_right (by omega)]
  · rw [z]; exact count_z (k := 1) hi (by decide) (by decide)

/-- The loop, after `q` is loaded. -/
theorem loop_ok {out : Nat → BitVec 32} {s₀ : State} {body : List Instr}
    (hb : ∀ i < 256, ∀ s, VG.Proof.MlDsa.Arm.Arith.Mul.Inv out s₀ i s → WP isa (.block body) s fun s' =>
      VG.Proof.MlDsa.Arm.Arith.Mul.Inv out s₀ (i + 1) s' ∧ s'.z = decide (i + 1 = 256)) :
    WP isa (.seq (.block (loadQ .r4 ++ ([.mov .r3 (.imm 256)] : List Instr))) (.loop (.block body) .ne)) s₀
      (VG.Proof.MlDsa.Arm.Arith.Mul.Inv out s₀ 256) := by
  refine WP.seq (WP.of_runBlock ?_)
  refine ⟨_, by simp only [loadQ, List.cons_append, List.nil_append, runBlock_cons, runStep_some,
    exec, Op2.eval, isa]; rfl,
    wp_loop_ne (VG.Proof.MlDsa.Arm.Arith.Mul.Inv out s₀) (N := 256) (by decide) hb (fun _ h => h) ?_⟩
  refine ⟨by simp [State.setReg], by simp [State.setReg], by simp [State.setReg], rfl, ?_, rfl, rfl, rfl,
    ⟨by simp [State.setReg], by simp [State.setReg], by simp [State.setReg]⟩, Frame.refl _ _, fun j _ => rfl⟩
  simp only [State.setReg]; exact loadQ_val

/-- The value stored in coefficient `j` by `vg_mldsa_multiply_ntt`. -/
def mulOut (s₀ : State) (j : Nat) : BitVec 32 :=
  BitVec.ofNat 32 ((multiplyNTT (polyAt s₀.mem (VG.Proof.MlDsa.Arm.Arith.Mul.F s₀)) (polyAt s₀.mem (VG.Proof.MlDsa.Arm.Arith.Mul.G s₀)))[j]!).val

/-- The value stored in coefficient `j` by `vg_mldsa_multiply_add_ntt`. -/
def mulAddOut (s₀ : State) (j : Nat) : BitVec 32 :=
  BitVec.ofNat 32 ((VG.Spec.MlDsa.add (polyAt s₀.mem (VG.Proof.MlDsa.Arm.Arith.Mul.H s₀)) (multiplyNTT (polyAt s₀.mem (VG.Proof.MlDsa.Arm.Arith.Mul.F s₀)) (polyAt s₀.mem (VG.Proof.MlDsa.Arm.Arith.Mul.G s₀))))[j]!).val

theorem prod_val {s₀ : State} (hp : VG.Proof.MlDsa.Arm.Arith.Mul.Pre s₀) {i : Nat} (hi : i < 256) {m : Mem} {y w : BitVec 32}
    (hy : m.readW (State.addr (y + BitVec.ofNat 32 0)) 32 = coeffAt s₀.mem (VG.Proof.MlDsa.Arm.Arith.Mul.F s₀) i)
    (hw : m.readW (State.addr (w + BitVec.ofNat 32 0)) 32 = coeffAt s₀.mem (VG.Proof.MlDsa.Arm.Arith.Mul.G s₀) i) :
    (bcsub (VG.Proof.MlDsa.Arm.Arith.Mul.prod m y w)).toNat = ((multiplyNTT (polyAt s₀.mem (VG.Proof.MlDsa.Arm.Arith.Mul.F s₀)) (polyAt s₀.mem (VG.Proof.MlDsa.Arm.Arith.Mul.G s₀)))[i]!).val := by
  simp only [VG.Proof.MlDsa.Arm.Arith.Mul.prod, hy, hw]
  rw [bcsub_mulz (hp.redG i hi) (hp.redF i hi), mul_get _ _ hi, val_mul, polyAt_val hp.redF hi,
    polyAt_val hp.redG hi, Nat.mul_comm]

theorem mul_hb {s₀ : State} (hp : VG.Proof.MlDsa.Arm.Arith.Mul.Pre s₀) : ∀ i < 256, ∀ s, VG.Proof.MlDsa.Arm.Arith.Mul.Inv (VG.Proof.MlDsa.Arm.Arith.Mul.mulOut s₀) s₀ i s →
    WP isa (.block mulBody) s fun s' => VG.Proof.MlDsa.Arm.Arith.Mul.Inv (VG.Proof.MlDsa.Arm.Arith.Mul.mulOut s₀) s₀ (i + 1) s' ∧ s'.z = decide (i + 1 = 256) := by
  intro i hi s h
  have a := VG.Proof.MlDsa.Arm.Arith.Mul.acc_of hp hi h
  refine VG.Proof.MlDsa.Arm.Arith.Mul.inv_step hp hi h (WP.mono (VG.Proof.MlDsa.Arm.Arith.Mul.body_ok h.r0 h.r1 h.r2 h.r3 h.r4 a.iF a.iG a.oH) fun s' hs => ?_)
  refine (?_ : _ = VG.Proof.MlDsa.Arm.Arith.Mul.mulOut s₀ i) ▸ hs
  exact ofNat_val_eq (VG.Proof.MlDsa.Arm.Arith.Mul.prod_val hp hi a.vF a.vG)

theorem mulAdd_hb {s₀ : State} (hp : VG.Proof.MlDsa.Arm.Arith.Mul.Pre s₀) (hH : Reduced s₀.mem (VG.Proof.MlDsa.Arm.Arith.Mul.H s₀)) :
    ∀ i < 256, ∀ s, VG.Proof.MlDsa.Arm.Arith.Mul.Inv (VG.Proof.MlDsa.Arm.Arith.Mul.mulAddOut s₀) s₀ i s →
    WP isa (.block mulAddBody) s fun s' => VG.Proof.MlDsa.Arm.Arith.Mul.Inv (VG.Proof.MlDsa.Arm.Arith.Mul.mulAddOut s₀) s₀ (i + 1) s' ∧ s'.z = decide (i + 1 = 256) := by
  intro i hi s h
  have a := VG.Proof.MlDsa.Arm.Arith.Mul.acc_of hp hi h
  refine VG.Proof.MlDsa.Arm.Arith.Mul.inv_step hp hi h (WP.mono (VG.Proof.MlDsa.Arm.Arith.Mul.bodyAdd_ok h.r0 h.r1 h.r2 h.r3 h.r4 a.iF a.iG a.oH a.iH) fun s' hs => ?_)
  refine (?_ : _ = VG.Proof.MlDsa.Arm.Arith.Mul.mulAddOut s₀ i) ▸ hs
  refine ofNat_val_eq ?_
  have hG := hp.redG i hi
  have hF := hp.redF i hi
  have hle := bmulz_le hG hF
  have hmod : (bmulz (coeffAt s₀.mem (VG.Proof.MlDsa.Arm.Arith.Mul.G s₀) i) (coeffAt s₀.mem (VG.Proof.MlDsa.Arm.Arith.Mul.F s₀) i >>> 14)
      (coeffAt s₀.mem (VG.Proof.MlDsa.Arm.Arith.Mul.F s₀) i <<< 18 >>> 25) (coeffAt s₀.mem (VG.Proof.MlDsa.Arm.Arith.Mul.F s₀) i <<< 25 >>> 25)).toNat % q =
      (coeffAt s₀.mem (VG.Proof.MlDsa.Arm.Arith.Mul.G s₀) i).toNat * (coeffAt s₀.mem (VG.Proof.MlDsa.Arm.Arith.Mul.F s₀) i).toNat % q := by
    rw [bmulz_toNat hG (Nat.lt_of_lt_of_le hF (by decide)), mulzN_mod]
  have hHi := hH i hi
  simp only [VG.Proof.MlDsa.Arm.Arith.Mul.prod, a.vF, a.vG, a.vH] at hle ⊢
  generalize bmulz _ _ _ _ = P at hle hmod ⊢
  have hs : (P + coeffAt s₀.mem (VG.Proof.MlDsa.Arm.Arith.Mul.H s₀) i).toNat = P.toNat + (coeffAt s₀.mem (VG.Proof.MlDsa.Arm.Arith.Mul.H s₀) i).toNat := by
    unfold redMax at hle; rw [q_eq] at hHi; bv_omega
  have hr := red23_le (x := (P + coeffAt s₀.mem (VG.Proof.MlDsa.Arm.Arith.Mul.H s₀) i).toNat) (BitVec.isLt _)
  rw [bcsub_toNat (by rw [bred_toNat]; exact Nat.lt_of_le_of_lt hr redMax_lt), bred_toNat, red23_mod, hs,
    add_get _ _ hi, val_add', mul_get _ _ hi, val_mul, polyAt_val hH hi, polyAt_val hp.redF hi,
    polyAt_val hp.redG hi, Nat.mul_comm (coeffAt s₀.mem (VG.Proof.MlDsa.Arm.Arith.Mul.F s₀) i).toNat]
  generalize (coeffAt s₀.mem (VG.Proof.MlDsa.Arm.Arith.Mul.G s₀) i).toNat * (coeffAt s₀.mem (VG.Proof.MlDsa.Arm.Arith.Mul.F s₀) i).toNat = X at *
  rw [q_eq] at *
  omega

/-! ## Verified -/

/-- The precondition of both functions, on entry. -/
structure PreE (s : State) : Prop where
  sp : 24 ≤ s.sp.toNat
  rd : s.rd = [polyRegion (VG.Proof.MlDsa.Arm.Arith.Mul.F s), polyRegion (VG.Proof.MlDsa.Arm.Arith.Mul.G s)]
  wr : s.wr = [polyRegion (VG.Proof.MlDsa.Arm.Arith.Mul.H s)]
  hf : (polyRegion (VG.Proof.MlDsa.Arm.Arith.Mul.H s)).Disjoint (polyRegion (VG.Proof.MlDsa.Arm.Arith.Mul.F s))
  hg : (polyRegion (VG.Proof.MlDsa.Arm.Arith.Mul.H s)).Disjoint (polyRegion (VG.Proof.MlDsa.Arm.Arith.Mul.G s))
  sH : (belowA s.sp 24).Disjoint (polyRegion (VG.Proof.MlDsa.Arm.Arith.Mul.H s))
  sF : (belowA s.sp 24).Disjoint (polyRegion (VG.Proof.MlDsa.Arm.Arith.Mul.F s))
  sG : (belowA s.sp 24).Disjoint (polyRegion (VG.Proof.MlDsa.Arm.Arith.Mul.G s))
  fitH : (VG.Proof.MlDsa.Arm.Arith.Mul.ph s).toNat + 1024 ≤ 2 ^ 32
  fitF : (VG.Proof.MlDsa.Arm.Arith.Mul.pf s).toNat + 1024 ≤ 2 ^ 32
  fitG : (VG.Proof.MlDsa.Arm.Arith.Mul.pg s).toNat + 1024 ≤ 2 ^ 32
  redF : Reduced s.mem (VG.Proof.MlDsa.Arm.Arith.Mul.F s)
  redG : Reduced s.mem (VG.Proof.MlDsa.Arm.Arith.Mul.G s)

theorem pre_of {s : State} (h : (Spec.MlDsa.mulContract Arm.abi 24).pre s) : VG.Proof.MlDsa.Arm.Arith.Mul.PreE s := by
  sig_pre [Spec.MlDsa.mulContract, Spec.MlDsa.mulSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val] at h
  obtain ⟨h1, -, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

theorem preAdd_of {s : State} (h : (Spec.MlDsa.mulAddContract Arm.abi 24).pre s) :
    VG.Proof.MlDsa.Arm.Arith.Mul.PreE s ∧ Reduced s.mem (VG.Proof.MlDsa.Arm.Arith.Mul.H s) := by
  sig_pre [Spec.MlDsa.mulAddContract, Spec.MlDsa.mulSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val] at h
  obtain ⟨h1, -, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h0, h12, h13⟩ := h
  exact ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩, h0⟩

/-- The loop's precondition, in the state after the pushes. -/
theorem pre_entry {s s₁ : State} (hp : VG.Proof.MlDsa.Arm.Arith.Mul.PreE s) (hE : VG.Proof.MlDsa.Arm.Arith.Entry 24 s s₁) :
    VG.Proof.MlDsa.Arm.Arith.Mul.Pre s₁ ∧ polyAt s₁.mem (VG.Proof.MlDsa.Arm.Arith.Mul.F s₁) = polyAt s.mem (VG.Proof.MlDsa.Arm.Arith.Mul.F s) ∧ polyAt s₁.mem (VG.Proof.MlDsa.Arm.Arith.Mul.G s₁) = polyAt s.mem (VG.Proof.MlDsa.Arm.Arith.Mul.G s) ∧
      polyAt s₁.mem (VG.Proof.MlDsa.Arm.Arith.Mul.H s₁) = polyAt s.mem (VG.Proof.MlDsa.Arm.Arith.Mul.H s) ∧ (Reduced s.mem (VG.Proof.MlDsa.Arm.Arith.Mul.H s) → Reduced s₁.mem (VG.Proof.MlDsa.Arm.Arith.Mul.H s₁)) := by
  have g := hE.gpr
  have eF : VG.Proof.MlDsa.Arm.Arith.Mul.F s₁ = VG.Proof.MlDsa.Arm.Arith.Mul.F s := by simp only [VG.Proof.MlDsa.Arm.Arith.Mul.F, VG.Proof.MlDsa.Arm.Arith.Mul.pf, g]
  have eG : VG.Proof.MlDsa.Arm.Arith.Mul.G s₁ = VG.Proof.MlDsa.Arm.Arith.Mul.G s := by simp only [VG.Proof.MlDsa.Arm.Arith.Mul.G, VG.Proof.MlDsa.Arm.Arith.Mul.pg, g]
  have eH : VG.Proof.MlDsa.Arm.Arith.Mul.H s₁ = VG.Proof.MlDsa.Arm.Arith.Mul.H s := by simp only [VG.Proof.MlDsa.Arm.Arith.Mul.H, VG.Proof.MlDsa.Arm.Arith.Mul.ph, g]
  have fr := hE.frame
  have dF : ∀ r ∈ [belowA s.sp 24], (polyRegion (VG.Proof.MlDsa.Arm.Arith.Mul.F s)).Disjoint r := fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; exact hp.sF.symm
  have dG : ∀ r ∈ [belowA s.sp 24], (polyRegion (VG.Proof.MlDsa.Arm.Arith.Mul.G s)).Disjoint r := fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; exact hp.sG.symm
  have dH : ∀ r ∈ [belowA s.sp 24], (polyRegion (VG.Proof.MlDsa.Arm.Arith.Mul.H s)).Disjoint r := fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; exact hp.sH.symm
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, by rw [eF]; exact polyAt_frame fr dF,
    by rw [eG]; exact polyAt_frame fr dG, by rw [eH]; exact polyAt_frame fr dH,
    fun h => by rw [eH]; exact reduced_frame fr dH h⟩
  · rw [hE.rd, hp.rd, eF, eG]
  · rw [eH]; exact hE.wr _ (by rw [hp.wr]; exact List.mem_singleton_self _)
  · rw [eH, eF]; exact hp.hf
  · rw [eH, eG]; exact hp.hg
  · simp only [VG.Proof.MlDsa.Arm.Arith.Mul.ph, g]; exact hp.fitH
  · simp only [VG.Proof.MlDsa.Arm.Arith.Mul.pf, g]; exact hp.fitF
  · simp only [VG.Proof.MlDsa.Arm.Arith.Mul.pg, g]; exact hp.fitG
  · rw [eF]; exact reduced_frame fr dF hp.redF
  · rw [eG]; exact reduced_frame fr dG hp.redG

theorem correct {s : State} (hp : VG.Proof.MlDsa.Arm.Arith.Mul.PreE s) :
    WP isa Impl.MlDsa.Arm.Arith.mul s fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧
      PolyIs s'.mem (VG.Proof.MlDsa.Arm.Arith.Mul.H s) (multiplyNTT (polyAt s.mem (VG.Proof.MlDsa.Arm.Arith.Mul.F s)) (polyAt s.mem (VG.Proof.MlDsa.Arm.Arith.Mul.G s))) := by
  refine WP.mono (VG.Proof.MlDsa.Arm.Arith.wp_saving mulSaved _ (W := [polyRegion (VG.Proof.MlDsa.Arm.Arith.Mul.H s)])
    (fun s₂ => VG.Proof.MlDsa.Arm.Arith.Mul.Keep s s₂ ∧ PolyIs s₂.mem (VG.Proof.MlDsa.Arm.Arith.Mul.H s) (multiplyNTT (polyAt s.mem (VG.Proof.MlDsa.Arm.Arith.Mul.F s)) (polyAt s.mem (VG.Proof.MlDsa.Arm.Arith.Mul.G s))))
    s hp.sp (fun R hR => by rw [List.mem_singleton] at hR; subst hR; exact hp.sH) fun s₁ hE => ?_)
    fun s' ⟨s₂, ⟨hk, hq⟩, hm, _, hsp, _, hg⟩ => ⟨VG.Proof.MlDsa.Arm.Arith.preserved_of_saving hg fun r hr hn => ?_, hsp, hm ▸ hq⟩
  · obtain ⟨hp₁, eF, eG, eH, -⟩ := VG.Proof.MlDsa.Arm.Arith.Mul.pre_entry hp hE
    have eH' : VG.Proof.MlDsa.Arm.Arith.Mul.H s₁ = VG.Proof.MlDsa.Arm.Arith.Mul.H s := by simp only [VG.Proof.MlDsa.Arm.Arith.Mul.H, VG.Proof.MlDsa.Arm.Arith.Mul.ph, hE.gpr]
    refine WP.mono (VG.Proof.MlDsa.Arm.Arith.Mul.loop_ok (VG.Proof.MlDsa.Arm.Arith.Mul.mul_hb hp₁)) fun s₂ h => ⟨?_, ?_, ?_⟩
    · rw [← eH']; exact h.frame
    · have k := h.keep
      simp only [VG.Proof.MlDsa.Arm.Arith.Mul.Keep, hE.gpr] at k ⊢
      exact k
    · rw [← eH', ← eF, ← eG]
      exact polyIs_of_toNat fun j hj => by
        rw [h.coeff j hj, ite_eq_left hj, VG.Proof.MlDsa.Arm.Arith.Mul.mulOut, toNat_val]
  · simp only [preserved, mulSaved, List.mem_cons, List.not_mem_nil, or_false] at hr hn
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp at hn
    · exact hk.1
    · exact hk.2.1
    · exact hk.2.2

theorem correctAdd {s : State} (hp : VG.Proof.MlDsa.Arm.Arith.Mul.PreE s) (hH : Reduced s.mem (VG.Proof.MlDsa.Arm.Arith.Mul.H s)) :
    WP isa Impl.MlDsa.Arm.Arith.mulAdd s fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧
      PolyIs s'.mem (VG.Proof.MlDsa.Arm.Arith.Mul.H s) (VG.Spec.MlDsa.add (polyAt s.mem (VG.Proof.MlDsa.Arm.Arith.Mul.H s)) (multiplyNTT (polyAt s.mem (VG.Proof.MlDsa.Arm.Arith.Mul.F s)) (polyAt s.mem (VG.Proof.MlDsa.Arm.Arith.Mul.G s)))) := by
  refine WP.mono (VG.Proof.MlDsa.Arm.Arith.wp_saving mulSaved _ (W := [polyRegion (VG.Proof.MlDsa.Arm.Arith.Mul.H s)])
    (fun s₂ => VG.Proof.MlDsa.Arm.Arith.Mul.Keep s s₂ ∧
      PolyIs s₂.mem (VG.Proof.MlDsa.Arm.Arith.Mul.H s) (VG.Spec.MlDsa.add (polyAt s.mem (VG.Proof.MlDsa.Arm.Arith.Mul.H s)) (multiplyNTT (polyAt s.mem (VG.Proof.MlDsa.Arm.Arith.Mul.F s)) (polyAt s.mem (VG.Proof.MlDsa.Arm.Arith.Mul.G s)))))
    s hp.sp (fun R hR => by rw [List.mem_singleton] at hR; subst hR; exact hp.sH) fun s₁ hE => ?_)
    fun s' ⟨s₂, ⟨hk, hq⟩, hm, _, hsp, _, hg⟩ => ⟨VG.Proof.MlDsa.Arm.Arith.preserved_of_saving hg fun r hr hn => ?_, hsp, hm ▸ hq⟩
  · obtain ⟨hp₁, eF, eG, eH, rH⟩ := VG.Proof.MlDsa.Arm.Arith.Mul.pre_entry hp hE
    have eH' : VG.Proof.MlDsa.Arm.Arith.Mul.H s₁ = VG.Proof.MlDsa.Arm.Arith.Mul.H s := by simp only [VG.Proof.MlDsa.Arm.Arith.Mul.H, VG.Proof.MlDsa.Arm.Arith.Mul.ph, hE.gpr]
    refine WP.mono (VG.Proof.MlDsa.Arm.Arith.Mul.loop_ok (VG.Proof.MlDsa.Arm.Arith.Mul.mulAdd_hb hp₁ (rH hH))) fun s₂ h => ⟨?_, ?_, ?_⟩
    · rw [← eH']; exact h.frame
    · have k := h.keep
      simp only [VG.Proof.MlDsa.Arm.Arith.Mul.Keep, hE.gpr] at k ⊢
      exact k
    · rw [← eH, ← eF, ← eG, ← eH']
      exact polyIs_of_toNat fun j hj => by
        rw [h.coeff j hj, ite_eq_left hj, VG.Proof.MlDsa.Arm.Arith.Mul.mulAddOut, toNat_val]
  · simp only [preserved, mulSaved, List.mem_cons, List.not_mem_nil, or_false] at hr hn
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp at hn
    · exact hk.1
    · exact hk.2.1
    · exact hk.2.2

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x2000, 1024⟩, ⟨0x3000, 1024⟩]
  wr := [⟨0x1000, 1024⟩]

theorem mul_verified : Verified Arm.target Impl.MlDsa.Arm.Arith.mul (Spec.MlDsa.mulContract Arm.abi 24) := by
  refine ⟨fun s hs => ?_, VG.Proof.MlDsa.Arm.Arith.ct_of_saving mulSaved _ [.r0, .r1, .r2] (fun s₁ s₂ h => ?_) (by taint_decide), ?_⟩
  · obtain ⟨t, s', he, hpres, hsp, h⟩ := VG.Proof.MlDsa.Arm.Arith.Mul.correct (VG.Proof.MlDsa.Arm.Arith.Mul.pre_of hs)
    refine ⟨t, s', he, ⟨hpres, hsp⟩, ?_⟩
    sig_post [Spec.MlDsa.mulContract, Spec.MlDsa.mulSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val]
    exact h
  · sig_pub [Spec.MlDsa.mulContract, Spec.MlDsa.mulSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] at h
    obtain ⟨hsp, h0, h1, h2⟩ := h
    refine ⟨hsp, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> with_reducible assumption
  · refine ⟨VG.Proof.MlDsa.Arm.Arith.Mul.satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Spec.MlDsa.mulContract, Spec.MlDsa.mulSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
        Arm.Loc.val]
      sig_and_intros
      all_goals first
        | trivial
        | exact VG.Proof.MlDsa.Arm.Arith.AddSub.reduced_zero _

theorem mulAdd_verified :
    Verified Arm.target Impl.MlDsa.Arm.Arith.mulAdd (Spec.MlDsa.mulAddContract Arm.abi 24) := by
  refine ⟨fun s hs => ?_, VG.Proof.MlDsa.Arm.Arith.ct_of_saving mulSaved _ [.r0, .r1, .r2] (fun s₁ s₂ h => ?_) (by taint_decide), ?_⟩
  · obtain ⟨hp, hH⟩ := VG.Proof.MlDsa.Arm.Arith.Mul.preAdd_of hs
    obtain ⟨t, s', he, hpres, hsp, h⟩ := VG.Proof.MlDsa.Arm.Arith.Mul.correctAdd hp hH
    refine ⟨t, s', he, ⟨hpres, hsp⟩, ?_⟩
    sig_post [Spec.MlDsa.mulAddContract, Spec.MlDsa.mulSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val]
    exact h
  · sig_pub [Spec.MlDsa.mulAddContract, Spec.MlDsa.mulSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] at h
    obtain ⟨hsp, h0, h1, h2⟩ := h
    refine ⟨hsp, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> with_reducible assumption
  · refine ⟨VG.Proof.MlDsa.Arm.Arith.Mul.satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Spec.MlDsa.mulAddContract, Spec.MlDsa.mulSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
        Arm.Loc.val]
      sig_and_intros
      all_goals first
        | trivial
        | exact VG.Proof.MlDsa.Arm.Arith.AddSub.reduced_zero _

end VG.Proof.MlDsa.Arm.Arith.Mul

end
