module

public import VerifiedGarbage.Proof.Dsa.Arm.Gen.SLoop
import VerifiedGarbage.Proof.Dsa.Arm.Gen.Pre
import VerifiedGarbage.Proof.Bignum.Arm.CopyBuffer
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Dsa.Generation.ParamsEncoding
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.KernelRfl
public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Slots

/-! # DSA parameter generation on ARMv7: the exit

`finish_vp`: the result's words into the frame (`dCfg`: the status, `used`,
`state[0]` and the next tape's length, computed for a tape that ran out by
`ranOut`), p‖q‖g copied from `sPacked` to `out` when the search found them,
else `out` zeroed (`OD`), then the words to `state` and `used`, their high
halves zero, and the status into `r0` (`FO`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm VG.WriteBytes
open VG.Impl.Dsa.Arm.Generation
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_mov wp_movw wp_dp wp_subs wp_strb op2_imm eval_eq eval_ne
  ofNat_beq_zero)
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Impl.Rsa.Arm.Keys (seqs)
open VG.Proof.RsaKeyGen.Arm (slot)

/-- What `out` holds for the controller's end. -/
def outBytes (G : GP) (o : COut) : List Byte :=
  match o with
  | .found a _ => Spec.Dsa.encodeParams G.pLen G.qLen a
  | _ => List.replicate G.outLen 0

/-- After the exit, the frame still allocated: `out`, `used` and `state`
hold the result (as 32-bit halves), `r0` the status. -/
structure FO (G : GP) (o : COut) (σ t : State) : Prop where
  pre : CIn σ
  hG : mkG σ = G
  sp : t.sp = G.sp
  rd : t.rd = σ.rd
  wr : t.wr = G.rFrame :: σ.wr
  saved : Spill.Saved t.mem (State.addr G.sp) σ.gpr VG.Impl.Dsa.Arm.Generation.saved
  frame : Frame (G.rOut :: G.rUsed :: G.rSt :: G.chg) σ.mem t.mem
  out : Spec.Rsa.bytesAt t.mem (State.addr G.out) G.outLen = outBytes G o
  u0 : slot t.mem (State.addr G.usedP) 0 = BitVec.ofNat 32 (cRes G o).used
  u1 : slot t.mem (State.addr G.usedP) 1 = 0
  s0 : slot t.mem (State.addr G.stP) 0 = BitVec.ofNat 32 (cRes G o).remaining
  s1 : slot t.mem (State.addr G.stP) 1 = 0
  s6 : slot t.mem (State.addr G.stP) 6 = BitVec.ofNat 32 (VG.Proof.Dsa.Generation.requested G.pLen (cRes G o))
  s7 : slot t.mem (State.addr G.stP) 7 = 0
  s25 : ∀ j, 2 ≤ j → j < 6 → slot t.mem (State.addr G.stP) j = slot σ.mem (State.addr G.stP) j
  r0 : t.gpr .r0 = BitVec.ofNat 32 (cRes G o).status

section
variable {G : GP} {σ s : State} {V : Nat → BitVec 32} {LS : List Nat} {X : State → Prop}

theorem GI.frame_out (h : GI G σ V LS s) : G.rFrame.Disjoint G.rOut := by
  rw [← h.hG]; exact h.pre.fO.sub_left (by rw [h.hG]; exact h.frameSub)

theorem GI.outLen (h : GI G σ V LS s) : G.outLen = 2 * G.pLen + G.qLen := by
  rw [← h.hG]; exact h.pre.outLen

theorem GI.outFit (h : GI G σ V LS s) : G.out.toNat + G.outLen ≤ 2 ^ 32 := by
  rw [← h.hG]; exact h.pre.nO

theorem GI.outW (h : GI G σ V LS s) : G.rOut ∈ s.wr := by
  rw [h.wr, h.pre.wr, h.hG]; simp

/-- `state` keeps its words through the search. -/
theorem GI.stWord {σ s : State} {V : Nat → BitVec 32} {LS : List Nat} (h : GI G σ V LS s) {d : Nat}
    (hd : d + 4 ≤ 32) : s.mem.readW (State.addr G.stP + BitVec.ofNat 64 d) 32 =
      σ.mem.readW (State.addr G.stP + BitVec.ofNat 64 d) 32 := by
  have pre := h.pre
  have fS := pre.fS; have cS := pre.cS; rw [h.hG] at fS cS
  have fit : G.stP.toNat + 32 ≤ 2 ^ 32 := by rw [← h.hG]; exact pre.nS
  have sub : Region.Sub ⟨State.addr G.stP + BitVec.ofNat 64 d, 4⟩ G.rSt := Offset.sub_base _ hd
  refine h.frame.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [GP.chg, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (fS.sub_left h.frameSub).symm.sub_left sub
  · exact cS.symm.sub_left sub
  · exact (fS.sub_left h.belowSub).symm.sub_left sub

theorem GI.saved_of {t : State} (h : GI G σ V LS s) {rs : List Region} (f : Frame rs s.mem t.mem)
    (hd : ∀ r ∈ rs, G.rFrame.Disjoint r) :
    Spill.Saved t.mem (State.addr G.sp) σ.gpr VG.Impl.Dsa.Arm.Generation.saved := fun p hp => by
  have hb : p.2 + 4 ≤ F := by
    simp only [VG.Impl.Dsa.Arm.Generation.saved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  show fw t.mem G p.2 = _
  rw [frame_readW f hd hb]
  exact h.saved p hp

end

/-! ## Zeroing `out` -/

theorem wp_inc {is : List Instr} {s : State} {Q : State → Prop} {d : Reg}
    (k : ∀ s', Upd s s' d (s.gpr d + 1) → WP isa (.block is) s' Q) :
    WP isa (.block (.dp .add d d (.imm 1) :: is)) s Q :=
  wp_dp (op2_imm (by decide)) k

theorem wp_dec {is : List Instr} {s : State} {Q : State → Prop} {d : Reg}
    (k : ∀ s', Upd s s' d (s.gpr d - 1) → s'.z = (s.gpr d - 1 == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.subs d d (.imm 1) :: is)) s Q :=
  wp_subs (op2_imm (by decide)) k

theorem ofNat32_sub_one {k : Nat} (hk : 1 ≤ k) : BitVec.ofNat 32 k - 1 = BitVec.ofNat 32 (k - 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [show (1 : BitVec 32).toNat = 1 from rfl]
  omega

/-- `k` bytes from `p` zeroed. -/
structure ZI (t : State) (p : BitVec 32) (N k : Nat) (u : State) : Prop where
  r0 : u.gpr .r0 = p + BitVec.ofNat 32 k
  lr : u.gpr .lr = BitVec.ofNat 32 (N - k)
  mem : u.mem = writeBytes t.mem (State.addr p) (List.replicate k 0)
  rest : Rest [.r0, .lr] t u

theorem zeroLoop_ok {t : State} {p : BitVec 32} {N : Nat} (hN : 0 < N) (hfit : p.toNat + N ≤ 2 ^ 32)
    (hw : ∀ k < N, InRegions t.wr (State.addr p + BitVec.ofNat 64 k) 1) (r0 : t.gpr .r0 = p)
    (r3 : t.gpr .r3 = 0) (lr : t.gpr .lr = BitVec.ofNat 32 N) :
    WP isa (.loop (.block zeroStep) .ne) t fun u =>
      u.mem = writeBytes t.mem (State.addr p) (List.replicate N 0) ∧ Rest [.r0, .lr] t u := by
  refine WP.loop (M := isa) (fun (n : Nat) (u : State) => ∃ k, n = N - k ∧ k < N ∧ ZI t p N k u)
    (fun n u hu => ?_) _ t ⟨0, rfl, hN, ⟨by rw [r0, BitVec.add_zero], by rw [lr, Nat.sub_zero],
      by rw [List.replicate_zero, writeBytes_nil], Rest.refl _ _⟩⟩
  obtain ⟨k, rfl, hk, I⟩ := hu
  unfold zeroStep
  refine wp_strb (a := State.addr p + BitVec.ofNat 64 k) (by decide)
    (by rw [BitVec.add_zero, I.r0, addr_add (by omega)]) (by rw [I.rest.wr]; exact hw k hk) fun u₁ m₁ =>
    wp_inc fun u₂ v₂ => wp_dec fun u₃ v₃ z₃ => WP.block_nil ?_
  have R : Rest [.r0, .lr] u u₃ := (m₁.rest _).trans ((v₂.rest (by simp)).trans (v₃.rest (by simp)))
  have J : ZI t p N (k + 1) u₃ := by
    refine ⟨?_, ?_, ?_, I.rest.trans R⟩
    · rw [v₃.other _ (by decide), v₂.gpr, m₁.gpr, I.r0, BitVec.add_assoc, BitVec.ofNat_add]; rfl
    · rw [v₃.gpr, v₂.other _ (by decide), m₁.gpr, I.lr, ofNat32_sub_one (by omega)]; rfl
    · have h3 : (u.gpr .r3).setWidth 8 = 0 := by rw [I.rest.gpr _ (by decide), r3]; rfl
      rw [v₃.mem, v₂.mem, m₁.mem, h3, I.mem, List.replicate_succ', writeBytes_snoc _ _ _ _ (by simp; omega),
        List.length_replicate]
  have hz : u₃.z = decide (N - (k + 1) = 0) := by
    rw [z₃, v₂.other _ (by decide), m₁.gpr, I.lr, ofNat32_sub_one (by omega), ofNat_beq_zero (by omega),
      Nat.sub_sub]
  by_cases he : N - (k + 1) = 0
  · left
    refine ⟨by rw [eval_ne, hz, decide_eq_true he]; rfl, ?_, J.rest⟩
    rw [J.mem, show k + 1 = N by omega]
  · right
    exact ⟨by rw [eval_ne, hz, decide_eq_false he]; rfl, _, by omega, k + 1, rfl, by omega, J⟩

/-! ## `out` -/

section
variable {G : GP} {X : State → Prop}

/-- `out` written with `ob`, from a stage `c` of the search at `t`. -/
def OD (G : GP) (c : Cfg) (X : State → Prop) (ob : List Byte) (σ u : State) : Prop :=
  ∃ t, St G c X σ t ∧ Rest [.r0, .r1, .r2, .r3, .r12, .lr] t u ∧ Frame [G.rOut] t.mem u.mem ∧
    Spec.Rsa.bytesAt u.mem (State.addr G.out) G.outLen = ob

/-- No parameters: `out` zeroed. -/
theorem outZero_vp {g : Geo} {c : Cfg} {F : State → State → Prop} (hF : ∀ σ s, F σ s → St G c X σ s)
    (hL : g.pLen = G.pLen) (hQ : g.qLen = G.qLen) :
    VP F g.outZero (OD G c X (List.replicate G.outLen 0)) := by
  unfold Geo.outZero
  refine VP.seq (G := fun σ t => ∃ s, St G c X σ s ∧ Upd s t .r0 G.out)
    (ld_vp (o := fOut) (fun σ s h => (hF σ s h).1) (by decide) (by decide)
      (fun σ s h => (hF σ s h).1.fixedV (by simp [fixedWords])) fun σ s t h u => ⟨s, hF σ s h, u⟩) ?_
  refine VP.taint [.r0] ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r0])
      (seqs [.block [.mov .r3 (.imm 0), .movw .lr (BitVec.ofNat 16 5)],
        .loop (.block zeroStep) .ne]), by kernel_rfl⟩ (fun σ₁ σ₂ s₁ s₂ ⟨_, _, u₁⟩ ⟨_, _, u₂⟩ r hr => ?_)
      fun σ t ⟨s, ⟨h, x⟩, u⟩ => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; rw [u₁.gpr, u₂.gpr]
  have gi := h.gi
  have hol := gi.outLen
  have fit := gi.outFit
  have hN : 0 < G.outLen := by rcases gi.lens with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ <;> omega
  have h16 : G.outLen < 2 ^ 16 := by rcases gi.lens with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ <;> omega
  refine WP.seq (wp_mov (op2_imm (by decide)) fun t₁ u₁ => wp_movw fun t₂ u₂ => WP.block_nil ?_)
  refine WP.mono (zeroLoop_ok (t := t₂) (p := G.out) hN fit (fun k hk => ⟨G.rOut, ?_, ?_⟩) ?_ ?_ ?_)
    fun t₃ ⟨m₃, R₃⟩ => ?_
  · rw [u₂.wr, u₁.wr, u.wr]; exact gi.outW
  · exact Offset.contains_base _ (by omega) (by omega)
  · rw [u₂.other _ (by decide), u₁.other _ (by decide), u.gpr]
  · rw [u₂.other _ (by decide), u₁.gpr]
  · rw [u₂.gpr]; apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, hL, hQ]; omega
  have R : Rest [.r0, .r3, .lr] s t₃ := (u.rest (by simp)).trans ((u₁.rest (by simp)).trans
    ((u₂.rest (by simp)).trans (R₃.mono (by simp))))
  have m₄ : t₃.mem = writeBytes s.mem (State.addr G.out) (List.replicate G.outLen 0) := by
    rw [m₃, u₂.mem, u₁.mem, u.mem]
  refine ⟨s, ⟨h, x⟩, R.mono (by simp), ?_, ?_⟩
  · rw [m₄]; exact writeBytes_frame _ _ _ (by rw [List.length_replicate]; exact Region.contains_self _ _)
  · rw [m₄]
    have := bytesAt_writeBytes s.mem (State.addr G.out) (List.replicate G.outLen 0) (d := 0) (k := G.outLen)
      (by simp) (by simp; omega)
    rw [BitVec.add_zero] at this
    rw [this]; simp

/-- Parameters at `sPacked`: copied to `out`. -/
theorem outCopy_vp {g : Geo} {c : Cfg} {a : Spec.Dsa.Params} {F : State → State → Prop}
    (hF : ∀ σ s, F σ s → St G c X σ s) (hcl : (sPacked, Spec.Dsa.encodeParams G.pLen G.qLen a) ∈ c.cl)
    (hL : g.pLen = G.pLen) (hQ : g.qLen = G.qLen) :
    VP F g.outCopy (OD G c X (Spec.Dsa.encodeParams G.pLen G.qLen a)) := by
  unfold Geo.outCopy
  have hlen := VG.Proof.Dsa.Generation.encodeParams_length G.pLen G.qLen a
  refine VP.seq (G := fun σ t => ∃ s, St G c X σ s ∧ Upd s t .r0 G.out)
    (ld_vp (o := fOut) (fun σ s h => (hF σ s h).1) (by decide) (by decide)
      (fun σ s h => (hF σ s h).1.fixedV (by simp [fixedWords])) fun σ s t h u => ⟨s, hF σ s h, u⟩)
    (VP.seq (G := (fun σ t => ∃ s, St G c X σ s ∧ Rest [.r0, .r1, .r12, .lr] s t ∧ t.mem = s.mem ∧
      t.gpr .r0 = G.out ∧ t.gpr .r1 = G.scr + BitVec.ofNat 32 sPacked ∧ t.gpr .lr = BitVec.ofNat 32 G.outLen :
      State → State → Prop)) ?_ ?_)
  · refine VP.taint [.r0, .r8] ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r0, .r8])
        (.block (scr 128 .r1 0 ++ [.movw .lr (BitVec.ofNat 16 5)])), by kernel_rfl⟩ (fun σ₁ σ₂ s₁ s₂ ⟨_, h₁,
            u₁⟩ ⟨_, h₂, u₂⟩ r hr => ?_) fun σ t ⟨s, ⟨h, x⟩, u⟩ => ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [u₁.gpr, u₂.gpr]
      · rw [u₁.other _ (by decide), u₂.other _ (by decide), h₁.1.r8, h₂.1.r8]
    have gi := h.gi
    have hol := gi.outLen
    have h16 : G.outLen < 2 ^ 16 := by rcases gi.lens with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ <;> omega
    have hpk : sPacked ≤ sK G.pLen := by
      have := h.clOk _ hcl; dsimp only at this; omega
    refine scr_ok (d := .r1) (by rw [u.other _ (by decide)]; exact h.r8) hL (hL ▸ h.lens) (hL ▸ hpk)
      fun s₁ v₁ R₁ M₁ => wp_movw fun s₂ u₂ => WP.block_nil
        ⟨s, ⟨h, x⟩, (u.rest (by simp)).trans ((R₁.mono (by simp)).trans (u₂.rest (by simp))),
          by rw [u₂.mem, M₁, u.mem], by rw [u₂.other _ (by decide), R₁.gpr _ (by decide), u.gpr],
          by rw [u₂.other _ (by decide)]; exact v₁, ?_⟩
    rw [u₂.gpr]; apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, hL, hQ]; omega
  · refine copyBytes_vp (src := G.scr + BitVec.ofNat 32 sPacked) (dst := G.out) (n := G.outLen)
      (fun σ t ⟨_, _, _, _, a, b, c⟩ => ⟨b, a, c⟩) fun σ s₂ ⟨s, ⟨h, x⟩, R, M, v0, v1, vl⟩ => ?_
    have gi := h.gi
    have hol := gi.outLen
    have big := gi.scrBig
    have fit := gi.scrFit
    have ofit := gi.outFit
    have hN : 0 < G.outLen := by rcases gi.lens with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ <;> omega
    have h16 : G.outLen < 2 ^ 16 := by rcases gi.lens with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ <;> omega
    have hpk : sPacked + G.outLen ≤ sK G.pLen := by
      have := h.clOk _ hcl; dsimp only at this; omega
    have ad := h.addr hpk hN
    have oc := gi.pre.oC
    rw [gi.hG] at oc
    refine WP.mono (VG.Proof.Bignum.Arm.copyBuffer_ok s₂ hN (by rw [h.toNat (by omega)]; omega) ofit (by omega)
      (by rw [ad, R.rd, R.wr]; obtain ⟨r, hr, hc⟩ := gi.inScr (o := sPacked) (n := G.outLen) (by omega)
          exact ⟨r, List.mem_append_right _ hr, hc⟩)
      ⟨G.rOut, by rw [R.wr]; exact gi.outW, Region.contains_self _ _⟩
      (by rw [ad]; exact oc.symm.sub_left (sw G (by omega))) v0 v1 vl)
      fun t ⟨rd', fr, _, rest⟩ => ⟨s, ⟨h, x⟩, (R.mono (by simp)).trans (rest.mono (by simp)), by rw [← M]; exact fr, ?_⟩
    rw [bytesAt_of_read rd', M, ad, hol, ← hlen]
    have e := h.sb _ hcl; dsimp only at e; exact e

end

/-! ## The result's words -/

section
variable {G : GP} {X : State → Prop}

/-- The result's words in the frame. -/
abbrev dCfg (G : GP) (o : COut) : Cfg :=
  ((((cFin G o).setV fRU (BitVec.ofNat 32 (cRes G o).used)).setV fRet (BitVec.ofNat 32 (cRes G o).status)).setV fR0
    (BitVec.ofNat 32 (cRes G o).remaining)).setV fR3
      (BitVec.ofNat 32 (VG.Proof.Dsa.Generation.requested G.pLen (cRes G o)))

/-- `results u v`: the result's words into the frame, `used` from the frame word `u`. -/
theorem results_vp {d : Cfg} {u : Nat} {U A B : BitVec 32} {v : Nat} (hv : v < 256) (hU : u ∈ d.LS)
    (hUv : d.V u = U) (hu : u + 4 ≤ F + 16) (hu4 : u % 4 = 0) {P : State → State → Prop}
    (hP : ∀ σ s, P σ s → St G d X σ s ∧ s.gpr .r2 = A ∧ s.gpr .r3 = B) :
    VP P (Geo.results u v)
      (St G ((((d.setV fRU U).setV fRet (BitVec.ofNat 32 v)).setV fR0 A).setV fR3 B) X) := by
  unfold Geo.results
  refine VP.seq (G := fun σ s => St G d X σ s ∧ s.gpr .r0 = U ∧ s.gpr .r2 = A ∧ s.gpr .r3 = B)
    (ld_vp (c := fun _ => d) (fun σ s h => (hP σ s h).1.1) hu hu4
      (fun σ s h => ((hP σ s h).1.1.slotV hU).trans hUv) fun σ s t h u' => ?_) ?_
  · obtain ⟨⟨h₁, x⟩, r2, r3⟩ := hP σ s h
    exact ⟨⟨h₁.of_rest (u'.rest (ws := [.r0]) (by simp)) u'.mem, x⟩, u'.gpr, by rw [u'.other _ (by decide), r2],
      by rw [u'.other _ (by decide), r3]⟩
  refine VP.seq (G := fun σ s => St G (d.setV fRU U) X σ s ∧ s.gpr .r2 = A ∧ s.gpr .r3 = B)
    (st_vp (c := fun _ => d) (fun σ s h => h.1.1) (by decide) (varOk_of (by decide))
      fun σ s t ⟨⟨_, x⟩, r0, r2, r3⟩ h' R => ⟨⟨r0 ▸ h', x⟩, by rw [R.gpr _ (by decide), r2],
        by rw [R.gpr _ (by decide), r3]⟩) ?_
  refine VP.seq (G := fun σ s => St G ((d.setV fRU U).setV fRet (BitVec.ofNat 32 v)) X σ s ∧ s.gpr .r2 = A ∧
      s.gpr .r3 = B)
    (stImm_vp (c := fun _ => d.setV fRU U) (fun σ s h => h.1.1) hv (varOk_of (by decide))
      fun σ s t ⟨⟨_, x⟩, r2, r3⟩ h' R => ⟨⟨h', x⟩, by rw [R.gpr _ (by decide), r2],
        by rw [R.gpr _ (by decide), r3]⟩) ?_
  refine VP.seq (G := fun σ s => St G (((d.setV fRU U).setV fRet (BitVec.ofNat 32 v)).setV fR0 A) X σ s ∧
      s.gpr .r3 = B)
    (st_vp (c := fun _ => (d.setV fRU U).setV fRet (BitVec.ofNat 32 v)) (fun σ s h => h.1.1) (by decide)
      (varOk_of (by decide)) fun σ s t ⟨⟨_, x⟩, r2, r3⟩ h' R => ⟨⟨r2 ▸ h', x⟩, by rw [R.gpr _ (by decide), r3]⟩) ?_
  exact st_vp (c := fun _ => ((d.setV fRU U).setV fRet (BitVec.ofNat 32 v)).setV fR0 A) (fun σ s h => h.1.1)
    (by decide) (varOk_of (by decide)) fun σ s t ⟨⟨_, x⟩, r3⟩ h' _ => ⟨r3 ▸ h', x⟩

/-- `mov r2, #0; mov r3, #0; results u v`. -/
theorem zres_vp {d : Cfg} {u : Nat} {U : BitVec 32} {v : Nat} (hv : v < 256) (hU : u ∈ d.LS)
    (hUv : d.V u = U) (hu : u + 4 ≤ F + 16) (hu4 : u % 4 = 0) {P : State → State → Prop}
    (hP : ∀ σ s, P σ s → St G d X σ s) :
    VP P (Geo.zres u v) (St G ((((d.setV fRU U).setV fRet (BitVec.ofNat 32 v)).setV fR0 0).setV fR3 0) X) := by
  refine VP.seq (G := fun σ s => St G d X σ s ∧ s.gpr .r2 = 0 ∧ s.gpr .r3 = 0)
    (VP.taint [] ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [])
      (.block [.mov .r2 (.imm 0), .mov .r3 (.imm 0)]), by kernel_rfl⟩ (fun _ _ _ _ _ _ r hr => absurd hr (by simp))
      fun σ s hs => ?_) (results_vp hv hU hUv hu hu4 fun σ s h => h)
  obtain ⟨h, x⟩ := hP σ s hs
  exact wp_mov (op2_imm (by decide)) fun s₁ u₁ => wp_mov (op2_imm (by decide)) fun t u => WP.block_nil
    ⟨⟨(h.of_rest (u₁.rest (ws := [.r2]) (by simp)) u₁.mem).of_rest (u.rest (ws := [.r3]) (by simp)) u.mem, x⟩,
      by rw [u.other _ (by decide), u₁.gpr], u.gpr⟩

theorem dCfg_ranOut (G : GP) (j c : Nat) :
    dCfg G (.ranOut j c) = if Spec.Dsa.parameterEntropy G.pLen ≤ G.witLen - c then
      ((((cFin G (.ranOut j c)).setV fRU (BitVec.ofNat 32 c)).setV fRet (BitVec.ofNat 32 3)).setV fR0 0).setV fR3 0
    else ((((cFin G (.ranOut j c)).setV fRU (BitVec.ofNat 32 c)).setV fRet (BitVec.ofNat 32 0)).setV fR0
      (BitVec.ofNat 32 j)).setV fR3
        (BitVec.ofNat 32 (VG.Proof.Dsa.Generation.parameterRequest G.pLen (G.witLen - c))) := by
  by_cases hb : Spec.Dsa.parameterEntropy G.pLen ≤ G.witLen - c <;>
    simp [dCfg, cRes, VG.Proof.Dsa.Generation.ranOutResult, hb, Spec.Entropy.Result.status,
      Spec.Entropy.Outcome.status, Spec.Dsa.ParameterSearchResult.remaining, VG.Proof.Dsa.Generation.requested,
      VG.Proof.Entropy.requested]

theorem dCfg_found (G : GP) (a : Spec.Dsa.Params) (u : Nat) :
    dCfg G (.found a u) = ((((cFin G (.found a u)).setV fRU (BitVec.ofNat 32 u)).setV fRet (BitVec.ofNat 32 1)).setV
      fR0 0).setV fR3 0 := by
  simp [dCfg, cRes, Spec.Entropy.Result.status, Spec.Entropy.Outcome.status,
    Spec.Dsa.ParameterSearchResult.remaining, VG.Proof.Dsa.Generation.requested, VG.Proof.Entropy.requested]

theorem dCfg_noSeeds (G : GP) (c : Nat) :
    dCfg G (.noSeeds c) = ((((cFin G (.noSeeds c)).setV fRU (BitVec.ofNat 32 c)).setV fRet (BitVec.ofNat 32 3)).setV
      fR0 0).setV fR3 0 := by
  simp [dCfg, cRes, Spec.Entropy.Result.status, Spec.Entropy.Outcome.status,
    Spec.Dsa.ParameterSearchResult.remaining, VG.Proof.Dsa.Generation.requested, VG.Proof.Entropy.requested]

/-- A block of register operations then `less`, its first part by `wp`: `Z`
iff `x < y`, with `r0 = x` and `r1 = y` after it. -/
theorem regLess_vp {P Q : State → State → Prop} {d : Cfg} {l : List Instr} {rs : List Reg} {x y : Nat}
    (hx : x < 2 ^ 32) (hy : y < 2 ^ 32)
    (cert : ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs rs) (.block l) hc).isSome = true)
    (regs : ∀ σ₁ σ₂ s₁ s₂, P σ₁ s₁ → P σ₂ s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (wp : ∀ σ s, P σ s → WP isa (.block l) s fun t => St G d X σ t ∧ t.gpr .r0 = BitVec.ofNat 32 x ∧
      t.gpr .r1 = BitVec.ofNat 32 y)
    (k : ∀ σ s, St G d X σ s ∧ s.gpr .r0 = BitVec.ofNat 32 x ∧ s.gpr .r1 = BitVec.ofNat 32 y ∧
      isa.eval .eq s = some (decide (x < y)) → Q σ s) :
    VP P (.block (l ++ less)) Q :=
  VP.block_append (G := fun σ s => St G d X σ s ∧ s.gpr .r0 = BitVec.ofNat 32 x ∧ s.gpr .r1 = BitVec.ofNat 32 y)
    (VP.taint rs cert regs wp)
    (less_vp (x := BitVec.ofNat 32 x) (y := BitVec.ofNat 32 y) (fun σ s h => h.2.1) (fun σ s h => h.2.2)
      fun σ s t ⟨⟨h, x'⟩, r0, r1⟩ R m e => k σ t ⟨⟨h.of_rest R m, x'⟩, by rw [R.gpr _ (by decide), r0],
        by rw [R.gpr _ (by decide), r1], by rw [e, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx,
          Nat.mod_eq_of_lt hy]⟩)

/-- `rand` ran out at the cursor `c` with `j` seeds left: the result's words. -/
theorem ranOut_vp {g : Geo} (hL : g.pLen = G.pLen) {j c : Nat} (hc : c ≤ G.witLen) (h32 : G.witLen < 2 ^ 32) :
    VP (St G (cFin G (.ranOut j c)) X) g.ranOut (St G (dCfg G (.ranOut j c)) X) := by
  by_cases l : G.pLen = 128 ∨ G.pLen = 256 ∨ G.pLen = 384
  swap
  · exact VP.of_false fun σ s h => l h.1.lens
  have hB : 32769 * G.pLen < 2 ^ 32 := by rcases l with e | e | e <;> rw [e] <;> decide
  generalize hd : cFin G (.ranOut j c) = d
  have hC : fC ∈ d.LS := by rw [← hd]; simp [cFin]
  have hCv : d.V fC = BitVec.ofNat 32 c := by rw [← hd]; simp [cFin, upd, fC, fSeedLeft, fStatus]
  have hS : fSeedLeft ∈ d.LS := by rw [← hd]; simp [cFin]
  have hSv : d.V fSeedLeft = BitVec.ofNat 32 j := by rw [← hd]; simp [cFin, upd, fSeedLeft, fStatus]
  rw [dCfg_ranOut, hd]
  unfold Geo.ranOut Geo.budget
  rw [hL]
  generalize ha : G.witLen - c = av
  have hav : av < 2 ^ 32 := by omega
  -- The octets left, against the budget.
  refine VP.seq (G := fun σ s => St G d X σ s ∧ s.gpr .r0 = BitVec.ofNat 32 G.witLen)
    (ld_vp (c := fun _ => d) (fun σ s h => h.1) (by decide) (by decide)
      (fun σ s h => h.1.fixedV (by simp [fixedWords]))
      fun σ s t ⟨h, x⟩ u => ⟨⟨h.of_rest (u.rest (ws := [.r0]) (by simp)) u.mem, x⟩, u.gpr⟩) ?_
  refine VP.seq (G := fun σ s => (St G d X σ s ∧ s.gpr .r0 = BitVec.ofNat 32 G.witLen) ∧
      s.gpr .r1 = BitVec.ofNat 32 c)
    (ld_vp (c := fun _ => d) (fun σ s h => h.1.1) (by decide) (by decide) (fun σ s h => (h.1.1.slotV hC).trans hCv)
      fun σ s t ⟨⟨h, x⟩, r0⟩ u => ⟨⟨⟨h.of_rest (u.rest (ws := [.r1]) (by simp)) u.mem, x⟩,
        by rw [u.other _ (by decide), r0]⟩, u.gpr⟩) ?_
  refine VP.seq (G := fun σ s => St G d X σ s ∧ s.gpr .r0 = BitVec.ofNat 32 av ∧
      s.gpr .r1 = BitVec.ofNat 32 (32769 * G.pLen) ∧ isa.eval .eq s = some (decide (av < 32769 * G.pLen)))
    (regLess_vp (d := d) (rs := [.r0, .r1]) hav hB ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r0, .r1])
      (.block ([.dp .sub .r0 .r0 (.reg .r1)] ++ cst .r1 0)), rfl⟩
      (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [h₁.1.2, h₂.1.2]
        · rw [h₁.2, h₂.2])
      (fun σ s ⟨⟨⟨h, x⟩, r0⟩, r1⟩ => ?_) fun σ s h => h) ?_
  · simp only [List.cons_append, List.nil_append]
    refine wp_dp (VG.Proof.X25519.Arm.op2_reg _ _) fun s₁ u₁ => ?_
    rw [← List.append_nil (cst .r1 _)]
    refine wp_cst hB fun t u => WP.block_nil ⟨⟨(h.of_rest (u₁.rest (ws := [.r0]) (by simp)) u₁.mem).of_rest
      (u.rest (ws := [.r1]) (by simp)) u.mem, x⟩, ?_, u.gpr⟩
    rw [u.other _ (by decide), u₁.gpr, VG.Proof.X25519.Arm.dpVal, r0, r1, ← ha]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  by_cases hb : Spec.Dsa.parameterEntropy G.pLen ≤ av
  · -- Exhausted.
    rw [ite_eq_left_of_eq_true _ _ (eq_true hb)]
    refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2.2.2, h₂.2.2.2])
      (VP.of_false fun σ s ⟨⟨_, _, _, e⟩, z⟩ => by
        rw [e] at z; simp only [Spec.Dsa.parameterEntropy] at hb; simp at z; omega)
      (zres_vp (by decide) hC hCv (by decide) (by decide) fun σ s h => h.1.1)
  rw [ite_eq_right_of_eq_false _ _ (eq_false hb)]
  simp only [Spec.Dsa.parameterEntropy, Nat.not_le] at hb
  refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2.2.2, h₂.2.2.2]) ?_
    (VP.of_false fun σ s ⟨⟨_, _, _, e⟩, z⟩ => by rw [e] at z; simp [hb] at z)
  have h256 : 256 * G.pLen < 2 ^ 32 := by omega
  -- At least `256 p_len`.
  refine VP.seq (G := fun σ s => St G d X σ s ∧ s.gpr .r0 = BitVec.ofNat 32 av ∧
      s.gpr .r1 = BitVec.ofNat 32 (256 * G.pLen) ∧ isa.eval .eq s = some (decide (av < 256 * G.pLen)))
    (regLess_vp (d := d) (rs := []) hav h256 ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [])
      (.block (cst .r1 0)), rfl⟩ (fun _ _ _ _ _ _ r hr => absurd hr (by simp))
      (fun σ s ⟨⟨⟨h, x⟩, r0, _⟩, _⟩ => by
        rw [← List.append_nil (cst .r1 _)]
        exact wp_cst h256 fun t u => WP.block_nil ⟨⟨h.of_rest (u.rest (ws := [.r1]) (by simp)) u.mem, x⟩,
          by rw [u.other _ (by decide), r0], u.gpr⟩) fun σ s h => h) ?_
  refine VP.seq (G := fun σ s => St G d X σ s ∧ s.gpr .r0 = BitVec.ofNat 32 (max av (256 * G.pLen)))
    (VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2.2.2, h₂.2.2.2])
      (VP.taint [.r1] ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r1]) (.block [.mov .r0 (.reg .r1)]),
        rfl⟩ (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by
          simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.2.2.1, h₂.1.2.2.1])
        fun σ s ⟨⟨⟨h, x⟩, _, r1, e⟩, z⟩ => wp_mov (VG.Proof.X25519.Arm.op2_reg _ _) fun t u => WP.block_nil
          ⟨⟨h.of_rest (u.rest (ws := [.r0]) (by simp)) u.mem, x⟩, ?_⟩)
      (VP.block_nil fun σ s ⟨⟨⟨h, x⟩, r0, _, e⟩, z⟩ => ⟨⟨h, x⟩, ?_⟩)) ?_
  · have : av < 256 * G.pLen := by rw [e] at z; simpa using z
    rw [u.gpr, r1, Nat.max_eq_right (Nat.le_of_lt this)]
  · have : ¬av < 256 * G.pLen := by rw [e] at z; simpa using z
    rw [r0, Nat.max_eq_left (by omega)]
  -- Twice that, at most the budget.
  have hM : 2 * max av (256 * G.pLen) < 2 ^ 32 := by
    rcases l with e | e | e <;> rw [e] at hb ⊢ <;> omega
  refine VP.seq (G := fun σ s => St G d X σ s ∧ s.gpr .r0 = BitVec.ofNat 32 (2 * max av (256 * G.pLen)) ∧
      s.gpr .r1 = BitVec.ofNat 32 (32769 * G.pLen) ∧
      isa.eval .eq s = some (decide (2 * max av (256 * G.pLen) < 32769 * G.pLen)))
    (regLess_vp (d := d) (rs := [.r0]) hM hB ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r0])
      (.block ([.dp .add .r0 .r0 (.reg .r0)] ++ cst .r1 0)), rfl⟩
      (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2, h₂.2])
      (fun σ s ⟨⟨h, x⟩, r0⟩ => ?_) fun σ s h => h) ?_
  · simp only [List.cons_append, List.nil_append]
    refine wp_dp (VG.Proof.X25519.Arm.op2_reg _ _) fun s₁ u₁ => ?_
    rw [← List.append_nil (cst .r1 _)]
    refine wp_cst hB fun t u => WP.block_nil ⟨⟨(h.of_rest (u₁.rest (ws := [.r0]) (by simp)) u₁.mem).of_rest
      (u.rest (ws := [.r1]) (by simp)) u.mem, x⟩, ?_, u.gpr⟩
    rw [u.other _ (by decide), u₁.gpr, VG.Proof.X25519.Arm.dpVal, r0]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have hreq : VG.Proof.Dsa.Generation.parameterRequest G.pLen av =
      min (2 * max av (256 * G.pLen)) (32769 * G.pLen) := rfl
  refine VP.seq (G := fun σ s => St G d X σ s ∧ s.gpr .r0 =
      BitVec.ofNat 32 (VG.Proof.Dsa.Generation.parameterRequest G.pLen av))
    (VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2.2.2, h₂.2.2.2])
      (VP.block_nil fun σ s ⟨⟨⟨h, x⟩, r0, _, e⟩, z⟩ => ⟨⟨h, x⟩, ?_⟩)
      (VP.taint [.r1] ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r1]) (.block [.mov .r0 (.reg .r1)]),
        rfl⟩ (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by
          simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.2.2.1, h₂.1.2.2.1])
        fun σ s ⟨⟨⟨h, x⟩, _, r1, e⟩, z⟩ => wp_mov (VG.Proof.X25519.Arm.op2_reg _ _) fun t u => WP.block_nil
          ⟨⟨h.of_rest (u.rest (ws := [.r0]) (by simp)) u.mem, x⟩, ?_⟩)) ?_
  · have : 2 * max av (256 * G.pLen) < 32769 * G.pLen := by rw [e] at z; simpa using z
    rw [r0, hreq, Nat.min_eq_left (Nat.le_of_lt this)]
  · have : ¬2 * max av (256 * G.pLen) < 32769 * G.pLen := by rw [e] at z; simpa using z
    rw [u.gpr, r1, hreq, Nat.min_eq_right (by omega)]
  -- The words.
  refine VP.seq (G := fun σ s => St G d X σ s ∧ s.gpr .r3 =
      BitVec.ofNat 32 (VG.Proof.Dsa.Generation.parameterRequest G.pLen av))
    (VP.taint [.r0] ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r0]) (.block [.mov .r3 (.reg .r0)]),
        rfl⟩ (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by
          simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2, h₂.2])
      fun σ s ⟨⟨h, x⟩, r0⟩ => wp_mov (VG.Proof.X25519.Arm.op2_reg _ _) fun t u => WP.block_nil
        ⟨⟨h.of_rest (u.rest (ws := [.r3]) (by simp)) u.mem, x⟩, by rw [u.gpr, r0]⟩) ?_
  refine VP.seq (G := fun σ s => St G d X σ s ∧ s.gpr .r2 = BitVec.ofNat 32 j ∧ s.gpr .r3 =
      BitVec.ofNat 32 (VG.Proof.Dsa.Generation.parameterRequest G.pLen av))
    (ld_vp (c := fun _ => d) (fun σ s h => h.1.1) (by decide) (by decide) (fun σ s h => (h.1.1.slotV hS).trans hSv)
      fun σ s t ⟨⟨h, x⟩, r3⟩ u => ⟨⟨h.of_rest (u.rest (ws := [.r2]) (by simp)) u.mem, x⟩, u.gpr,
        by rw [u.other _ (by decide), r3]⟩) ?_
  exact results_vp (by decide) hC hCv (by decide) (by decide) fun σ s h => h

end

/-! ## The words to `state` and `used` -/

section
variable {G : GP} {σ s : State} {V : Nat → BitVec 32} {LS : List Nat} {X : State → Prop}

theorem GI.frame_st (h : GI G σ V LS s) : G.rFrame.Disjoint G.rSt := by
  rw [← h.hG]; exact h.pre.fS.sub_left (by rw [h.hG]; exact h.frameSub)

theorem GI.frame_used (h : GI G σ V LS s) : G.rFrame.Disjoint G.rUsed := by
  rw [← h.hG]; exact h.pre.fU.sub_left (by rw [h.hG]; exact h.frameSub)

theorem GI.stFit (h : GI G σ V LS s) : G.stP.toNat + 32 ≤ 2 ^ 32 := by
  rw [← h.hG]; exact h.pre.nS

theorem GI.usedFit (h : GI G σ V LS s) : G.usedP.toNat + 8 ≤ 2 ^ 32 := by
  rw [← h.hG]; exact h.pre.nU

theorem GI.stW (h : GI G σ V LS s) : G.rSt ∈ s.wr := by
  rw [h.wr, h.pre.wr, h.hG]; simp

theorem GI.usedW (h : GI G σ V LS s) : G.rUsed ∈ s.wr := by
  rw [h.wr, h.pre.wr, h.hG]; simp

end

/-- The pair of words `(r0, r2)` stored at `B + d` through `r1`. -/
theorem wp_pair {u : State} {B : BitVec 32} {d : Nat} {rest : List Instr} {Q : State → Prop} (hd : d + 4 < 4096)
    (r1 : u.gpr .r1 = B) (hfit : B.toNat + d + 8 ≤ 2 ^ 32)
    (h0 : InRegions u.wr (State.addr B + BitVec.ofNat 64 d) 4)
    (h1 : InRegions u.wr (State.addr B + BitVec.ofNat 64 (d + 4)) 4)
    (k : ∀ u', u'.gpr = u.gpr → u'.sp = u.sp → u'.rd = u.rd → u'.wr = u.wr →
      u'.mem = (u.mem.writeW (State.addr B + BitVec.ofNat 64 d) (u.gpr .r0)).writeW
        (State.addr B + BitVec.ofNat 64 (d + 4)) (u.gpr .r2) → WP isa (.block rest) u' Q) :
    WP isa (.block (.str .r0 .r1 d :: .str .r2 .r1 (d + 4) :: rest)) u Q := by
  refine VG.Proof.X25519.Arm.wp_str (a := State.addr B + BitVec.ofNat 64 d) (by omega)
    (by rw [r1]; exact addr_add (by omega)) h0 fun u₁ m₁ => ?_
  refine VG.Proof.X25519.Arm.wp_str (a := State.addr B + BitVec.ofNat 64 (d + 4)) (by omega)
    (by rw [m₁.gpr, r1]; exact addr_add (by omega))
    (by rw [m₁.wr]; exact h1) fun u₂ m₂ => k u₂ (by rw [m₂.gpr, m₁.gpr]) (by rw [m₂.sp, m₁.sp])
      (by rw [m₂.rd, m₁.rd]) (by rw [m₂.wr, m₁.wr]) (by rw [m₂.mem, m₁.mem, m₁.gpr])

/-- The slots of a pair just stored. -/
theorem slot_pair {m : Mem} {B : Addr} {N i j : Nat} (hN : 4 * N ≤ 2 ^ 64) (hi : i + 1 < N) (hj : j < N)
    (v w : BitVec 32) :
    slot ((m.writeW (B + BitVec.ofNat 64 (4 * i)) v).writeW (B + BitVec.ofNat 64 (4 * i + 4)) w) B j =
      if j = i + 1 then w else if j = i then v else slot m B j := by
  have e := VG.Proof.RsaKeyGen.Arm.slot_store (m.writeW (B + BitVec.ofNat 64 (4 * i)) v) B w hN hi hj
  rw [show 4 * (i + 1) = 4 * i + 4 by omega] at e
  rw [e, VG.Proof.RsaKeyGen.Arm.slot_store m B v hN (by omega) hj]

/-- A pair of words stored apart from `B`'s `N` words. -/
theorem slot_pair_apart {m : Mem} {B U : Addr} {N j : Nat} (hj : j < N) (hN : 4 * N < 2 ^ 64)
    (hd : Region.Disjoint ⟨B, 4 * N⟩ ⟨U, 8⟩) (v w : BitVec 32) :
    slot ((m.writeW (U + BitVec.ofNat 64 0) v).writeW (U + BitVec.ofNat 64 4) w) B j = slot m B j := by
  have f : Frame [⟨U, 8⟩] m ((m.writeW (U + BitVec.ofNat 64 0) v).writeW (U + BitVec.ofNat 64 4) w) :=
    ((Frame.refl _ m).writeW List.mem_cons_self v (Offset.contains_base _ (by decide) (by decide))).writeW
      List.mem_cons_self w (Offset.contains_base _ (by decide) (by decide))
  exact f.readW (r := ⟨B, 4 * N⟩) (Offset.contains_base _ (by omega) (by omega))
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hd) (by decide)

section
variable {G : GP} {X : State → Prop}

/-- A stage of the write-back: from `u₀`, where `out` is written, registers
changed and `state` and `used` written but for `state[1]` and `state[2]`, with
`P`. -/
def WBA (G : GP) (o : COut) (X : State → Prop) (P : State → Prop) (σ u : State) : Prop :=
  ∃ u₀, OD G (dCfg G o) X (outBytes G o) σ u₀ ∧ Rest [.r0, .r1, .r2] u₀ u ∧ Frame [G.rSt, G.rUsed] u₀.mem u.mem ∧
    (∀ j, 2 ≤ j → j < 6 → slot u.mem (State.addr G.stP) j = slot u₀.mem (State.addr G.stP) j) ∧ P u

/-- The facts a stage of the write-back rests on. -/
structure WBF (G : GP) (o : COut) (σ t u : State) : Prop where
  gi : SS G σ (dCfg G o) t
  sp : u.sp = G.sp
  rd : u.rd = t.rd
  wr : u.wr = t.wr
  fw : ∀ o', o' + 4 ≤ F → fw u.mem G o' = fw t.mem G o'

theorem WBA.facts {o : COut} {P : State → Prop} {σ u : State} (h : WBA G o X P σ u) :
    ∃ t, WBF G o σ t u ∧ X σ := by
  obtain ⟨u₀, ⟨t, ⟨ht, x⟩, R, f, _⟩, R', f', _, _⟩ := h
  have gi := ht.gi
  refine ⟨t, ⟨ht, by rw [R'.sp, R.sp, gi.sp], by rw [R'.rd, R.rd], by rw [R'.wr, R.wr], fun o' ho => ?_⟩, x⟩
  rw [frame_readW f' (fun r hr => ?_) ho, frame_readW f (fun r hr => ?_) ho]
  · simp only [List.mem_singleton] at hr; subst hr; exact gi.frame_out
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [gi.frame_st, gi.frame_used]

theorem WBA.spOk {o : COut} {P : State → Prop} : SpOk G (WBA G o X P) := fun σ u h => by
  obtain ⟨t, W, _⟩ := h.facts; exact W.sp

/-- A load of a frame word in the write-back. -/
theorem WBA.ldH {o : COut} {P : State → Prop} {σ u : State} (h : WBA G o X P σ u) {o' : Nat} (ho : o' + 4 ≤ F)
    (h4 : o' % 4 = 0) {v : BitVec 32} (hv : ∀ t, SS G σ (dCfg G o) t → fw t.mem G o' = v) {r : Reg}
    {rest : List Instr} {Q : State → Prop} (k : ∀ u', Upd u u' r v → WP isa (.block rest) u' Q) :
    WP isa (.block (.ldrSp r o' :: rest)) u Q := by
  obtain ⟨t, W, _⟩ := h.facts
  have hi := W.gi.gi.spHi
  refine VG.Proof.Bignum.Arm.wp_loadStack (a := State.addr G.sp + BitVec.ofNat 64 o') (by simp only [F] at ho; omega)
    (by rw [W.sp]; exact addr_add (by omega)) (by rw [W.rd, W.wr]; exact W.gi.gi.read (by omega) h4)
    fun u' up => k u' ?_
  have e : u.mem.readW (State.addr G.sp + BitVec.ofNat 64 o') 32 = v := (W.fw o' ho).trans (hv t W.gi)
  rwa [e] at up

/-- A step of the write-back that keeps what was written. -/
theorem WBA.step {o : COut} {P P' : State → Prop} {σ u u' : State} (h : WBA G o X P σ u) {ws : List Reg}
    (R : Rest ws u u') (hws : ∀ r ∈ ws, r ∈ [Reg.r0, .r1, .r2]) (f : Frame [G.rSt, G.rUsed] u.mem u'.mem)
    (hk : ∀ j, 2 ≤ j → j < 6 → slot u'.mem (State.addr G.stP) j = slot u.mem (State.addr G.stP) j)
    (p : P' u') : WBA G o X P' σ u' := by
  obtain ⟨u₀, hod, R₀, f₀, k₀, _⟩ := h
  exact ⟨u₀, hod, R₀.trans (R.mono hws), f₀.trans f, fun j a b => (hk j a b).trans (k₀ j a b), p⟩

theorem WBA.upd {o : COut} {P P' : State → Prop} {σ u u' : State} (h : WBA G o X P σ u) {r : Reg} {v : BitVec 32}
    (up : Upd u u' r v) (hr : r ∈ [Reg.r0, .r1, .r2]) (p : P' u') : WBA G o X P' σ u' :=
  h.step (ws := [r]) (up.rest (by simp)) (by simpa using hr) (by rw [up.mem]; exact Frame.refl _ _)
    (fun j _ _ => by rw [up.mem]) p

theorem WBA.p {o : COut} {P : State → Prop} {σ u : State} (h : WBA G o X P σ u) : P u := by
  obtain ⟨_, _, _, _, _, p⟩ := h; exact p

/-- What the stores rest on. -/
structure WBW (G : GP) (u : State) : Prop where
  stFit : G.stP.toNat + 32 ≤ 2 ^ 32
  usedFit : G.usedP.toNat + 8 ≤ 2 ^ 32
  stW : G.rSt ∈ u.wr
  usedW : G.rUsed ∈ u.wr
  uS : G.rUsed.Disjoint G.rSt

theorem WBA.wbw {o : COut} {P : State → Prop} {σ u : State} (h : WBA G o X P σ u) : WBW G u := by
  obtain ⟨t, W, _⟩ := h.facts
  have gi := W.gi.gi
  have uS := gi.pre.uS; rw [gi.hG] at uS
  exact ⟨gi.stFit, gi.usedFit, by rw [W.wr]; exact gi.stW, by rw [W.wr]; exact gi.usedW, uS⟩

/-- A pair stored into `state`. -/
theorem WBA.stPair {o : COut} {P P' : State → Prop} {σ u : State} (h : WBA G o X P σ u) {i : Nat} (hi : i = 0 ∨ i = 6)
    (r1 : u.gpr .r1 = G.stP) {rest : List Instr} {Q : State → Prop}
    (p : ∀ u', u'.gpr = u.gpr → u'.mem = (u.mem.writeW (State.addr G.stP + BitVec.ofNat 64 (4 * i)) (u.gpr .r0)).writeW
      (State.addr G.stP + BitVec.ofNat 64 (4 * i + 4)) (u.gpr .r2) → P' u')
    (k : ∀ u', WBA G o X P' σ u' → WP isa (.block rest) u' Q) :
    WP isa (.block (.str .r0 .r1 (4 * i) :: .str .r2 .r1 (4 * i + 4) :: rest)) u Q := by
  have w := h.wbw
  have c : ∀ d, d + 4 ≤ 32 → G.rSt.Contains (State.addr G.stP + BitVec.ofNat 64 d) 4 := fun d hd =>
    Offset.contains_base _ hd (by have := w.stFit; omega)
  refine wp_pair (by omega) r1 (by have := w.stFit; omega) ⟨G.rSt, w.stW, c _ (by omega)⟩
    ⟨G.rSt, w.stW, c _ (by omega)⟩ fun u' g sp rd wr m => k u' (h.step (ws := []) ⟨fun r _ => by rw [g], rd, wr, sp⟩
      (by simp) ?_ (fun j a b => ?_) (p u' g m))
  · rw [m]
    exact ((Frame.refl _ _).writeW List.mem_cons_self _ (c _ (by omega))).writeW List.mem_cons_self _ (c _ (by omega))
  · rw [m, slot_pair (N := 8) (by decide) (by omega) (by omega)]
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), ite_eq_right_of_eq_false _ _ (eq_false (by omega))]

/-- The pair stored into `used`. -/
theorem WBA.usedPair {o : COut} {P P' : State → Prop} {σ u : State} (h : WBA G o X P σ u)
    (r1 : u.gpr .r1 = G.usedP) {rest : List Instr} {Q : State → Prop}
    (p : ∀ u', u'.gpr = u.gpr → u'.mem = (u.mem.writeW (State.addr G.usedP + BitVec.ofNat 64 0) (u.gpr .r0)).writeW
      (State.addr G.usedP + BitVec.ofNat 64 4) (u.gpr .r2) → P' u')
    (k : ∀ u', WBA G o X P' σ u' → WP isa (.block rest) u' Q) :
    WP isa (.block (.str .r0 .r1 0 :: .str .r2 .r1 4 :: rest)) u Q := by
  have w := h.wbw
  have c : ∀ d, d + 4 ≤ 8 → G.rUsed.Contains (State.addr G.usedP + BitVec.ofNat 64 d) 4 := fun d hd =>
    Offset.contains_base _ hd (by have := w.usedFit; omega)
  refine wp_pair (d := 0) (by omega) r1 (by have := w.usedFit; omega) ⟨G.rUsed, w.usedW, c _ (by omega)⟩
    ⟨G.rUsed, w.usedW, c _ (by omega)⟩ fun u' g sp rd wr m => k u' (h.step (ws := []) ⟨fun r _ => by rw [g], rd, wr, sp⟩
      (by simp) ?_ (fun j a b => ?_) (p u' g m))
  · rw [m]
    exact ((Frame.refl _ _).writeW (List.mem_cons_of_mem _ List.mem_cons_self) _ (c _ (by omega))).writeW
      (List.mem_cons_of_mem _ List.mem_cons_self) _ (c _ (by omega))
  · rw [m]; exact slot_pair_apart (N := 8) (by omega) (by decide) w.uS.symm _ _

theorem slot_pair_lo {m : Mem} {B : Addr} {N i : Nat} (hN : 4 * N ≤ 2 ^ 64) (hi : i + 1 < N) (v w : BitVec 32) :
    slot ((m.writeW (B + BitVec.ofNat 64 (4 * i)) v).writeW (B + BitVec.ofNat 64 (4 * i + 4)) w) B i = v := by
  rw [slot_pair hN hi (by omega), ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
    ite_eq_left_of_eq_true _ _ (eq_true rfl)]

theorem slot_pair_hi {m : Mem} {B : Addr} {N i : Nat} (hN : 4 * N ≤ 2 ^ 64) (hi : i + 1 < N) (v w : BitVec 32) :
    slot ((m.writeW (B + BitVec.ofNat 64 (4 * i)) v).writeW (B + BitVec.ofNat 64 (4 * i + 4)) w) B (i + 1) = w := by
  rw [slot_pair hN hi hi, ite_eq_left_of_eq_true _ _ (eq_true rfl)]

theorem slot_pair_ne {m : Mem} {B : Addr} {N i j : Nat} (hN : 4 * N ≤ 2 ^ 64) (hi : i + 1 < N) (hj : j < N)
    (h1 : j ≠ i) (h2 : j ≠ i + 1) (v w : BitVec 32) :
    slot ((m.writeW (B + BitVec.ofNat 64 (4 * i)) v).writeW (B + BitVec.ofNat 64 (4 * i + 4)) w) B j =
      slot m B j := by
  rw [slot_pair hN hi hj, ite_eq_right_of_eq_false _ _ (eq_false h2), ite_eq_right_of_eq_false _ _ (eq_false h1)]

section
variable {G : GP} {X : State → Prop}

/-- The words written: `state[0]` and `state[3]`, then `used`. -/
abbrev wbDone (G : GP) (o : COut) (u : State) : Prop :=
  slot u.mem (State.addr G.stP) 0 = BitVec.ofNat 32 (cRes G o).remaining ∧ slot u.mem (State.addr G.stP) 1 = 0 ∧
    slot u.mem (State.addr G.stP) 6 = BitVec.ofNat 32 (VG.Proof.Dsa.Generation.requested G.pLen (cRes G o)) ∧
    slot u.mem (State.addr G.stP) 7 = 0 ∧
    slot u.mem (State.addr G.usedP) 0 = BitVec.ofNat 32 (cRes G o).used ∧ slot u.mem (State.addr G.usedP) 1 = 0

/-- The last stage of the write-back: `FO`. -/
theorem fo_of {o : COut} {σ u : State} (h : WBA G o X (wbDone G o) σ u)
    (r0 : u.gpr .r0 = BitVec.ofNat 32 (cRes G o).status) : FO G o σ u ∧ X σ := by
  obtain ⟨u₀, ⟨t, ⟨ht, x⟩, R, f, ob⟩, R', f', k25, s0, s1, s6, s7, v0, v1⟩ := h
  have gi := ht.gi
  have pre := gi.pre
  have oS := pre.oS; have oU := pre.oU
  rw [gi.hG] at oS oU
  have fo : Frame [G.rOut, G.rSt, G.rUsed] t.mem u.mem :=
    (f.mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp).trans
      (f'.mono fun r hr => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl <;> simp)
  refine ⟨⟨pre, gi.hG, by rw [R'.sp, R.sp, gi.sp], by rw [R'.rd, R.rd, gi.rd], by rw [R'.wr, R.wr, gi.wr],
    gi.saved_of fo (fun r hr => ?_), (gi.frame.mono fun r hr => ?_).trans (fo.mono fun r hr => ?_), ?_,
    v0, v1, s0, s1, s6, s7, fun j a b => ?_, r0⟩, x⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [gi.frame_out, gi.frame_st, gi.frame_used]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp
  · rw [VG.Proof.Dsa.Generation.frame_bytesAt f' (fun r hr => ?_) (by have := gi.outFit; omega)]
    · exact ob
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [oS, oU]
  · have fit := gi.stFit
    rw [k25 j a b]
    show u₀.mem.readW _ 32 = σ.mem.readW _ 32
    rw [← gi.stWord (d := 4 * j) (by omega)]
    exact f.readW (r := ⟨State.addr G.stP + BitVec.ofNat 64 (4 * j), 4⟩) (Region.contains_self _ _)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact oS.symm.sub_left (Offset.sub_base _ (by omega))) (by decide)

/-- The words to `state` and `used`, and the status into `r0`. -/
theorem writeBack_vp (o : COut) :
    VP (OD G (dCfg G o) X (outBytes G o)) Geo.writeBack (fun σ t => FO G o σ t ∧ X σ) := by
  refine (show VP (WBA G o X fun _ => True) _ _ from ?_).mono
    (fun σ u h => ⟨u, h, Rest.refl _ _, Frame.refl _ _, fun _ _ _ => rfl, trivial⟩) (fun _ _ h => h)
  unfold Geo.writeBack
  have vR0 : ∀ σ t, SS G σ (dCfg G o) t → fw t.mem G fR0 = BitVec.ofNat 32 (cRes G o).remaining :=
    fun σ t h => (h.slotV (by simp)).trans (by simp [upd, fR0, fR3])
  have vR3 : ∀ σ t, SS G σ (dCfg G o) t → fw t.mem G fR3 =
      BitVec.ofNat 32 (VG.Proof.Dsa.Generation.requested G.pLen (cRes G o)) :=
    fun σ t h => (h.slotV (by simp)).trans (by simp [upd])
  have vRU : ∀ σ t, SS G σ (dCfg G o) t → fw t.mem G fRU = BitVec.ofNat 32 (cRes G o).used :=
    fun σ t h => (h.slotV (by simp)).trans (by simp [upd, fR0, fR3, fRet, fRU])
  have vRet : ∀ σ t, SS G σ (dCfg G o) t → fw t.mem G fRet = BitVec.ofNat 32 (cRes G o).status :=
    fun σ t h => (h.slotV (by simp)).trans (by simp [upd, fR0, fR3, fRet])
  -- `r1` := `state`.
  refine VP.seq (G := WBA G o X fun u => u.gpr .r1 = G.stP)
    (VP.ld (G := G) WBA.spOk fun σ u h => h.ldH (o' := fStP) (by decide) (by decide)
      (fun t ht => ht.fixedV (by simp [fixedWords])) fun u' up => WP.block_nil (h.upd up (by simp) up.gpr)) ?_
  -- `r0` := `state[0]`.
  refine VP.seq (G := WBA G o X fun u => u.gpr .r1 = G.stP ∧ u.gpr .r0 = BitVec.ofNat 32 (cRes G o).remaining)
    (VP.ld (G := G) WBA.spOk fun σ u h => h.ldH (o' := fR0) (by decide) (by decide) (vR0 σ) fun u' up =>
      WP.block_nil (h.upd up (by simp) ⟨by rw [up.other _ (by decide)]; exact h.p, up.gpr⟩)) ?_
  -- `state[0]`.
  refine VP.seq (G := WBA G o X fun u => u.gpr .r1 = G.stP ∧ u.gpr .r2 = 0 ∧
      slot u.mem (State.addr G.stP) 0 = BitVec.ofNat 32 (cRes G o).remaining ∧ slot u.mem (State.addr G.stP) 1 = 0)
    (VP.taint [.r1] ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r1])
      (.block [.mov .r2 (.imm 0), .str .r0 .r1 0, .str .r2 .r1 4]), rfl⟩
      (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h₁.p.1, h₂.p.1])
      fun σ u h => wp_mov (op2_imm (by decide)) fun u₁ up₁ => ?_) ?_
  · have h₁ : WBA G o X (fun u => u.gpr .r1 = G.stP ∧ u.gpr .r0 = BitVec.ofNat 32 (cRes G o).remaining ∧
        u.gpr .r2 = 0) σ u₁ :=
      h.upd up₁ (by simp) ⟨by rw [up₁.other _ (by decide)]; exact h.p.1, by rw [up₁.other _ (by decide)]; exact h.p.2,
        up₁.gpr⟩
    exact h₁.stPair (i := 0) (.inl rfl) h₁.p.1 (fun u' g m => ⟨by rw [g]; exact h₁.p.1, by rw [g]; exact h₁.p.2.2,
      by rw [m, slot_pair_lo (N := 8) (i := 0) (by decide) (by decide), h₁.p.2.1],
      by rw [m, show (1 : Nat) = 0 + 1 from rfl, slot_pair_hi (N := 8) (i := 0) (by decide) (by decide), h₁.p.2.2]⟩)
      fun u' h' => WP.block_nil h'
  -- `r0` := `state[3]`.
  refine VP.seq (G := WBA G o X fun u => u.gpr .r1 = G.stP ∧ u.gpr .r2 = 0 ∧
      u.gpr .r0 = BitVec.ofNat 32 (VG.Proof.Dsa.Generation.requested G.pLen (cRes G o)) ∧
      slot u.mem (State.addr G.stP) 0 = BitVec.ofNat 32 (cRes G o).remaining ∧ slot u.mem (State.addr G.stP) 1 = 0)
    (VP.ld (G := G) WBA.spOk fun σ u h => h.ldH (o' := fR3) (by decide) (by decide) (vR3 σ) fun u' up =>
      WP.block_nil (h.upd up (by simp) ⟨by rw [up.other _ (by decide)]; exact h.p.1,
        by rw [up.other _ (by decide)]; exact h.p.2.1, up.gpr, by rw [up.mem]; exact h.p.2.2.1,
        by rw [up.mem]; exact h.p.2.2.2⟩)) ?_
  -- `state[3]`.
  refine VP.seq (G := WBA G o X fun u => u.gpr .r2 = 0 ∧
      slot u.mem (State.addr G.stP) 0 = BitVec.ofNat 32 (cRes G o).remaining ∧ slot u.mem (State.addr G.stP) 1 = 0 ∧
      slot u.mem (State.addr G.stP) 6 = BitVec.ofNat 32 (VG.Proof.Dsa.Generation.requested G.pLen (cRes G o)) ∧
      slot u.mem (State.addr G.stP) 7 = 0)
    (VP.taint [.r1] ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r1])
      (.block [.str .r0 .r1 24, .str .r2 .r1 28]), rfl⟩
      (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h₁.p.1, h₂.p.1])
      fun σ u h => h.stPair (i := 6) (.inr rfl) h.p.1 (fun u' g m => ⟨by rw [g]; exact h.p.2.1,
        by rw [m, slot_pair_ne (N := 8) (i := 6) (by decide) (by decide) (by decide) (by decide) (by decide)]
           exact h.p.2.2.2.1,
        by rw [m, slot_pair_ne (N := 8) (i := 6) (by decide) (by decide) (by decide) (by decide) (by decide)]
           exact h.p.2.2.2.2,
        by rw [m, slot_pair_lo (N := 8) (i := 6) (by decide) (by decide), h.p.2.2.1],
        by rw [m, show (7 : Nat) = 6 + 1 from rfl, slot_pair_hi (N := 8) (i := 6) (by decide) (by decide), h.p.2.1]⟩)
        fun u' h' => WP.block_nil h') ?_
  -- `r1` := `used`, `r0` := its word.
  refine VP.seq (G := WBA G o X fun u => u.gpr .r1 = G.usedP ∧ u.gpr .r2 = 0 ∧
      slot u.mem (State.addr G.stP) 0 = BitVec.ofNat 32 (cRes G o).remaining ∧ slot u.mem (State.addr G.stP) 1 = 0 ∧
      slot u.mem (State.addr G.stP) 6 = BitVec.ofNat 32 (VG.Proof.Dsa.Generation.requested G.pLen (cRes G o)) ∧
      slot u.mem (State.addr G.stP) 7 = 0)
    (VP.ld (G := G) WBA.spOk fun σ u h => h.ldH (o' := fUsedP) (by decide) (by decide)
      (fun t ht => ht.fixedV (by simp [fixedWords])) fun u' up => WP.block_nil (h.upd up (by simp)
        ⟨up.gpr, by rw [up.other _ (by decide)]; exact h.p.1, by rw [up.mem]; exact h.p.2.1,
          by rw [up.mem]; exact h.p.2.2.1, by rw [up.mem]; exact h.p.2.2.2.1, by rw [up.mem]; exact h.p.2.2.2.2⟩)) ?_
  refine VP.seq (G := WBA G o X fun u => u.gpr .r1 = G.usedP ∧ u.gpr .r2 = 0 ∧
      u.gpr .r0 = BitVec.ofNat 32 (cRes G o).used ∧
      slot u.mem (State.addr G.stP) 0 = BitVec.ofNat 32 (cRes G o).remaining ∧ slot u.mem (State.addr G.stP) 1 = 0 ∧
      slot u.mem (State.addr G.stP) 6 = BitVec.ofNat 32 (VG.Proof.Dsa.Generation.requested G.pLen (cRes G o)) ∧
      slot u.mem (State.addr G.stP) 7 = 0)
    (VP.ld (G := G) WBA.spOk fun σ u h => h.ldH (o' := fRU) (by decide) (by decide) (vRU σ) fun u' up =>
      WP.block_nil (h.upd up (by simp) ⟨by rw [up.other _ (by decide)]; exact h.p.1,
        by rw [up.other _ (by decide)]; exact h.p.2.1, up.gpr, by rw [up.mem]; exact h.p.2.2.1,
        by rw [up.mem]; exact h.p.2.2.2.1, by rw [up.mem]; exact h.p.2.2.2.2.1,
        by rw [up.mem]; exact h.p.2.2.2.2.2⟩)) ?_
  -- `used`.
  refine VP.seq (G := WBA G o X (wbDone G o))
    (VP.taint [.r1] ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r1])
      (.block [.str .r0 .r1 0, .str .r2 .r1 4]), rfl⟩
      (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h₁.p.1, h₂.p.1])
      fun σ u h => h.usedPair h.p.1 (fun u' g m => ?_) fun u' h' => WP.block_nil h') ?_
  · have uS := h.wbw.uS
    have a : ∀ j, j < 8 → slot u'.mem (State.addr G.stP) j = slot u.mem (State.addr G.stP) j := fun j hj => by
      rw [m]; exact slot_pair_apart (N := 8) hj (by decide) uS.symm _ _
    refine ⟨by rw [a 0 (by decide)]; exact h.p.2.2.2.1, by rw [a 1 (by decide)]; exact h.p.2.2.2.2.1,
      by rw [a 6 (by decide)]; exact h.p.2.2.2.2.2.1, by rw [a 7 (by decide)]; exact h.p.2.2.2.2.2.2, ?_, ?_⟩
    · rw [m]
      exact (slot_pair_lo (N := 2) (i := 0) (by decide) (by decide) _ _).trans h.p.2.2.1
    · rw [m]
      exact (slot_pair_hi (N := 2) (i := 0) (by decide) (by decide) _ _).trans h.p.2.1
  -- The status.
  exact VP.ld (G := G) WBA.spOk fun σ u h => h.ldH (o' := fRet) (by decide) (by decide) (vRet σ) fun u' up =>
    WP.block_nil (fo_of (h.upd up (by simp) (by unfold wbDone; rw [up.mem]; exact h.p)) up.gpr)

end

/-- The exit. -/
theorem finish_vp {g : Geo} (hL : g.pLen = G.pLen) (hQ : g.qLen = G.qLen) (o : COut) (hok : cOk G o)
    (h32 : G.witLen < 2 ^ 32) :
    VP (St G (cFin G o) X) g.finish (fun σ t => FO G o σ t ∧ X σ) := by
  unfold Geo.finish
  have hc : ∀ {F : State → State → Prop} {b : Bool}, (∀ σ s, F σ s → isa.eval .eq s = some b) →
      ∀ σ₁ σ₂ s₁ s₂, F σ₁ s₁ → F σ₂ s₂ → isa.eval .eq s₁ = isa.eval .eq s₂ :=
    fun hF _ _ _ _ h₁ h₂ => by rw [hF _ _ h₁, hF _ _ h₂]
  have no : ∀ {F : State → State → Prop} {c : Prog isa} {Q : State → State → Prop} {b : Bool},
      VP (fun σ s => (F σ s ∧ isa.eval .eq s = some b) ∧ isa.eval .eq s = some (!b)) c Q := by
    intro F c Q b
    exact VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; cases b <;> simp at z
  cases o with
  | found a u =>
    refine VP.seq (G := fun σ s => St G (cFin G (.found a u)) X σ s ∧ isa.eval .eq s = some true)
      (cmpF_vp (x := BitVec.ofNat 32 1) (fun σ s h => h.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.slotV (by simp [cFin])).trans (by simp [cFin]))
        fun σ s t ⟨h, x⟩ R m e => ⟨⟨h.of_rest R m, x⟩, by rw [e]; rfl⟩) ?_
    refine VP.seq (G := St G (dCfg G (.found a u)) X) (VP.ite (hc fun σ s h => h.2)
      ((zres_vp (u := fUsed) (U := BitVec.ofNat 32 u) (by decide) (by simp [cFin])
        (by simp [cFin, upd, fUsed, fStatus]) (by decide) (by decide) fun σ s h => h.1.1).mono (fun _ _ h => h)
          fun σ s h => by rw [dCfg_found]; exact h) no) ?_
    refine VP.seq (G := fun σ s => St G (dCfg G (.found a u)) X σ s ∧ isa.eval .eq s = some true)
      (cmpF_vp (x := BitVec.ofNat 32 1) (fun σ s h => h.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.slotV (by simp [cFin])).trans (by simp [cFin, upd, fStatus, fR3, fR0, fRet, fRU]))
        fun σ s t ⟨h, x⟩ R m e => ⟨⟨h.of_rest R m, x⟩, by rw [e]; rfl⟩) ?_
    exact VP.seq (VP.ite (hc fun σ s h => h.2)
      (outCopy_vp (fun σ s h => h.1.1) (by simp [cFin]) hL hQ) no) (writeBack_vp _)
  | noSeeds c =>
    refine VP.seq (G := fun σ s => St G (cFin G (.noSeeds c)) X σ s ∧ isa.eval .eq s = some false)
      (cmpF_vp (x := BitVec.ofNat 32 3) (fun σ s h => h.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.slotV (by simp [cFin])).trans (by simp [cFin]))
        fun σ s t ⟨h, x⟩ R m e => ⟨⟨h.of_rest R m, x⟩, by rw [e]; rfl⟩) ?_
    refine VP.seq (G := St G (dCfg G (.noSeeds c)) X) (VP.ite (hc fun σ s h => h.2) no ?_) ?_
    · refine VP.seq (G := fun σ s => St G (cFin G (.noSeeds c)) X σ s ∧ isa.eval .eq s = some false)
        (cmpF_vp (x := BitVec.ofNat 32 3) (fun σ s h => h.1.1.1) (by decide) (by decide) (by decide)
          (fun σ s h => (h.1.1.1.slotV (by simp [cFin])).trans (by simp [cFin]))
          fun σ s t ⟨⟨⟨h, x⟩, _⟩, _⟩ R m e => ⟨⟨h.of_rest R m, x⟩, by rw [e]; rfl⟩) ?_
      exact VP.ite (hc fun σ s h => h.2) no
        ((zres_vp (u := fC) (U := BitVec.ofNat 32 c) (by decide) (by simp [cFin])
          (by simp [cFin, upd, fC, fStatus]) (by decide) (by decide) fun σ s h => h.1.1).mono (fun _ _ h => h)
            fun σ s h => by rw [dCfg_noSeeds]; exact h)
    refine VP.seq (G := fun σ s => St G (dCfg G (.noSeeds c)) X σ s ∧ isa.eval .eq s = some false)
      (cmpF_vp (x := BitVec.ofNat 32 3) (fun σ s h => h.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.slotV (by simp [cFin])).trans (by simp [cFin, upd, fStatus, fR3, fR0, fRet, fRU]))
        fun σ s t ⟨h, x⟩ R m e => ⟨⟨h.of_rest R m, x⟩, by rw [e]; rfl⟩) ?_
    exact VP.seq (VP.ite (hc fun σ s h => h.2) no (outZero_vp (fun σ s h => h.1.1) hL hQ)) (writeBack_vp _)
  | ranOut j c =>
    refine VP.seq (G := fun σ s => St G (cFin G (.ranOut j c)) X σ s ∧ isa.eval .eq s = some false)
      (cmpF_vp (x := BitVec.ofNat 32 2) (fun σ s h => h.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.slotV (by simp [cFin])).trans (by simp [cFin]))
        fun σ s t ⟨h, x⟩ R m e => ⟨⟨h.of_rest R m, x⟩, by rw [e]; rfl⟩) ?_
    refine VP.seq (G := St G (dCfg G (.ranOut j c)) X) (VP.ite (hc fun σ s h => h.2) no ?_) ?_
    · refine VP.seq (G := fun σ s => St G (cFin G (.ranOut j c)) X σ s ∧ isa.eval .eq s = some true)
        (cmpF_vp (x := BitVec.ofNat 32 2) (fun σ s h => h.1.1.1) (by decide) (by decide) (by decide)
          (fun σ s h => (h.1.1.1.slotV (by simp [cFin])).trans (by simp [cFin]))
          fun σ s t ⟨⟨⟨h, x⟩, _⟩, _⟩ R m e => ⟨⟨h.of_rest R m, x⟩, by rw [e]; rfl⟩) ?_
      exact VP.ite (hc fun σ s h => h.2) ((ranOut_vp hL hok.1 h32).mono (fun σ s h => h.1.1) fun _ _ h => h) no
    refine VP.seq (G := fun σ s => St G (dCfg G (.ranOut j c)) X σ s ∧ isa.eval .eq s = some false)
      (cmpF_vp (x := BitVec.ofNat 32 2) (fun σ s h => h.1) (by decide) (by decide) (by decide)
        (fun σ s h => (h.1.slotV (by simp [cFin])).trans (by simp [cFin, upd, fStatus, fR3, fR0, fRet, fRU]))
        fun σ s t ⟨h, x⟩ R m e => ⟨⟨h.of_rest R m, x⟩, by rw [e]; rfl⟩) ?_
    exact VP.seq (VP.ite (hc fun σ s h => h.2) no (outZero_vp (fun σ s h => h.1.1) hL hQ)) (writeBack_vp _)

end

end VG.Proof.Dsa.Arm.Gen
