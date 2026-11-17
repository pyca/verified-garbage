module

public import VerifiedGarbage.Proof.Cast5.RISCV64.KeyStep
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Cast5.RISCV64.Ecb
import VerifiedGarbage.Proof.Cast5.RISCV64.Scan
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RISCV64.Align
public import VerifiedGarbage.Impl.Cast5.RISCV64
public import VerifiedGarbage.Proof.Cast5.RISCV64.Run
public import VerifiedGarbage.Proof.Cast5.Table
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill

/-! ### `Cast5.RISCV64.KeyHalf`, which only this module used -/

section

/-!
# CAST5 key expansion on RISC-V: the steps of a half, run

`keyStep_ok`: step `j` of a half (its number in `stp`) is the spec's
`stepRun`; `half_ok`: the 40 steps of a half compute `halfImpl`
(`runSteps_half`), writing its sixteen subkeys from `out`. As on RISCV64
(`Proof/Cast5/RISCV64/KeyHalf.lean`).
-/

@[expose] public section

namespace VG.Proof.Cast5.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Cast5 VG.Impl.Cast5.RISCV64 VG.Proof.Cast5

/-! ## Facts about the steps, by evaluation -/

def isKey : Step → Bool
  | .line _ (.key _) => true
  | _ => false

/-- The number of subkey steps. -/
def countKeys (ss : List Step) : Nat := (ss.filter isKey).length

theorem ws_length : ∀ (ss : List Step) (k : KSt), (runSteps ss k).ws.length = k.ws.length + countKeys ss
  | [], _ => rfl
  | s :: ss, k => by
    rw [runSteps_cons, ws_length ss]
    unfold countKeys
    rcases s with ⟨⟩ | ⟨l, ⟨⟩ | ⟨⟩⟩ <;> simp [stepRun, isKey, List.filter_cons] <;> omega_arith

/-- The bytes a step looks up: `S5[a], S6[b], S7[c], S8[d]`. -/
def stepPos : Step → Pos × Pos × Pos × Pos
  | .extras a b c d => (a, b, c, d)
  | .line l _ => l.main

theorem Step.gather_eq (st : Step) :
    st.gather = gather (stepPos st).1 (stepPos st).2.1 (stepPos st).2.2.1 (stepPos st).2.2.2 := by
  cases st <;> rfl

/-- What each step needs, and the place of each subkey, checked by evaluation. -/
def stepsOk : Bool :=
  halfSteps.length == 40 && (List.range 40).all fun j =>
    let st := halfSteps.getD j default
    stepOk st && (stepPos st).1.2 < 16 && (stepPos st).2.1.2 < 16 && (stepPos st).2.2.1.2 < 16 &&
      (stepPos st).2.2.2.2 < 16 &&
      match st with
      | .line _ (.key jj) => countKeys (halfSteps.take j) == jj
      | _ => true

theorem stepsOk_true : stepsOk = true := by decide +kernel

theorem halfSteps_length : halfSteps.length = 40 := by
  have := stepsOk_true
  simp only [stepsOk, Bool.and_eq_true, beq_iff_eq] at this
  exact this.1

theorem step_facts {j : Nat} (hj : j < 40) :
    stepOk (halfSteps.getD j default) = true ∧ (stepPos (halfSteps.getD j default)).1.2 < 16 ∧
      (stepPos (halfSteps.getD j default)).2.1.2 < 16 ∧ (stepPos (halfSteps.getD j default)).2.2.1.2 < 16 ∧
      (stepPos (halfSteps.getD j default)).2.2.2.2 < 16 ∧
      (∀ l jj, halfSteps.getD j default = .line l (.key jj) → countKeys (halfSteps.take j) = jj) := by
  have := stepsOk_true
  simp only [stepsOk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at this
  obtain h := this.2 j hj
  simp only [decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨h1, h2, h3, h4, h5, fun l jj e => ?_⟩
  rw [e] at h6
  simpa using h6

theorem take_succ_steps {j : Nat} (hj : j < 40) :
    halfSteps.take (j + 1) = halfSteps.take j ++ [halfSteps.getD j default] := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by rw [halfSteps_length]; exact hj)]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [halfSteps_length]; exact hj)]

theorem getD_map_steps {α : Type} (f : Step → α) (d : α) {j : Nat} (hj : j < 40) :
    (halfSteps.map f).getD j d = f (halfSteps.getD j default) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [halfSteps_length]; exact hj)]

theorem ofNat_setWidth8 (x : Byte) : BitVec.ofNat 8 (x.setWidth 64).toNat = x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_setWidth]
  have := x.isLt
  omega_arith

theorem setWidth8_lt (x : Byte) : (x.setWidth 64).toNat < 256 := by
  rw [BitVec.toNat_setWidth]; have := x.isLt; omega_arith

/-! ## A step -/

theorem keyStep_ok {m0 : Mem} {cb kb T : Addr} {u : State} {k0 : KSt} {j hh : Nat} (hj : j < 40)
    (h : KS m0 cb kb T u (runSteps (halfSteps.take j) k0)) (h2 : u.gpr stp = BitVec.ofNat 64 j)
    (hout : u.gpr out = kb + BitVec.ofNat 64 (64 * hh)) (hlen0 : k0.ws.length = 16 * hh) (hhh : hh < 2) :
    WP isa Impl.Cast5.RISCV64.step u fun v => KS m0 cb kb T v (runSteps (halfSteps.take (j + 1)) k0) ∧
      v.gpr stp = BitVec.ofNat 64 (j + 1) ∧ v.gpr tmp = BitVec.ofNat 64 (j + 1) - BitVec.ofNat 64 40 ∧
      Keep stepRegs u v := by
  obtain ⟨hok, p1, p2, p3, p4, hkeys⟩ := step_facts hj
  obtain ⟨st, hst⟩ : ∃ st, halfSteps.getD j default = st := ⟨_, rfl⟩
  rw [hst] at hok p1 p2 p3 p4 hkeys
  obtain ⟨kj, hkj⟩ : ∃ kj, runSteps (halfSteps.take j) k0 = kj := ⟨_, rfl⟩
  rw [hkj] at h
  obtain hnext : runSteps (halfSteps.take (j + 1)) k0 = stepRun st kj := by
    rw [take_succ_steps hj, runSteps_append, hkj, hst]; rfl
  rw [hnext]
  obtain hlen40 : 0 + (halfSteps.map Step.gather).length ≤ 2048 := by simp [halfSteps_length]
  unfold Impl.Cast5.RISCV64.step
  -- The step's bytes.
  refine WP.seq (sel_ok _ 0 (Nat.zero_le j) (by simp [halfSteps_length]; omega_arith) hlen40 h2
    fun u1 k1 m1 => ?_)
  rw [Nat.sub_zero, getD_map_steps _ _ hj, hst, Step.gather_eq]
  obtain h1 : KS m0 cb kb T u1 kj := h.update k1 (by rw [m1]; exact h.mem) (fun i hi => by rw [m1]; exact h.ex i hi)
    h.len
  refine WP.mono (gather_ok h1 p1 p2 p3 p4) fun v ⟨v4, v5, v6, v7, vk, vm⟩ => ?_
  obtain hv : KS m0 cb kb T v kj := h1.update vk (by rw [vm]; exact h1.mem)
    (fun i hi => by rw [vm]; exact h1.ex i hi) h1.len
  -- The scan.
  obtain hidx : ∀ i < 4, (v.gpr (idxReg i)).toNat < 256 := by
    intro i hi
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega_arith) with rfl | rfl | rfl | rfl
    · show (v.gpr .s0).toNat < 256; rw [v4]; exact setWidth8_lt _
    · show (v.gpr .s1).toNat < 256; rw [v5]; exact setWidth8_lt _
    · show (v.gpr .s2).toNat < 256; rw [v6]; exact setWidth8_lt _
    · show (v.gpr .s3).toNat < 256; rw [v7]; exact setWidth8_lt _
  obtain sp : ScanPre v := ⟨hidx, by rw [hv.tblR]; exact hv.tal, by rw [hv.tblR]; exact hv.trd⟩
  refine WP.seq (WP.mono (scan_ok v sp) fun w ⟨wa, wk, wm⟩ => ?_)
  obtain hw : KS m0 cb kb T w kj := hv.update wk (by rw [wm]; exact hv.mem) (fun i hi => by rw [wm]; exact hv.ex i hi)
    hv.len
  have ent (i : Nat) (hi : i < 4) (x : Byte) (hx : v.gpr (idxReg i) = x.setWidth 64) :
      lo (w.gpr (accReg i)) = tableEnt Spec.Cast5.S8 Spec.Cast5.S7 Spec.Cast5.S6 Spec.Cast5.S5
        (x.setWidth 64).toNat i := by
    rw [wa i hi, hx, lo_ext, hv.tblR]; exact ent_table hv.held (setWidth8_lt _) hi
  obtain a0 : lo (w.gpr .s4) = Spec.Cast5.S8 (kj.xz.get (stepPos st).2.2.2) := by
    rw [show Reg.s4 = accReg 0 from rfl, ent 0 (by decide) _ v4]; simp only [tableEnt, ofNat_setWidth8]
  obtain a1 : lo (w.gpr .s5) = Spec.Cast5.S7 (kj.xz.get (stepPos st).2.2.1) := by
    rw [show Reg.s5 = accReg 1 from rfl, ent 1 (by decide) _ v5]; simp only [tableEnt, ofNat_setWidth8]
  obtain a2 : lo (w.gpr .s6) = Spec.Cast5.S6 (kj.xz.get (stepPos st).2.1) := by
    rw [show Reg.s6 = accReg 2 from rfl, ent 2 (by decide) _ v6]; simp only [tableEnt, ofNat_setWidth8]
  obtain a3 : lo (w.gpr .s7) = Spec.Cast5.S5 (kj.xz.get (stepPos st).1) := by
    rw [show Reg.s7 = accReg 3 from rfl, ent 3 (by decide) _ v7]; simp only [tableEnt, ofNat_setWidth8]
  obtain kuw' := (k1.trans vk).trans wk
  obtain kuw : Keep stepRegs u w := kuw'.mono (by decide)
  obtain w2 : w.gpr stp = BitVec.ofNat 64 j := by rw [kuw'.gpr (by decide), h2]
  obtain wout : w.gpr out = kb + BitVec.ofNat 64 (64 * hh) := by rw [kuw'.gpr (by decide), hout]
  -- What it does with the values.
  refine WP.seq (sel_ok _ 0 (Nat.zero_le j) (by simp [halfSteps_length]; omega_arith) (by simp [halfSteps_length]) w2
    fun x kx mx => ?_)
  rw [Nat.sub_zero, getD_map_steps _ _ hj, hst]
  obtain hx : KS m0 cb kb T x kj := hw.update kx (by rw [mx]; exact hw.mem) (fun i hi => by rw [mx]; exact hw.ex i hi)
    hw.len
  have gx (q : Reg) (hq : q ≠ tmp) : x.gpr q = w.gpr q := kx.gpr (by simpa using hq)
  have tail (y : State) (hy : KS m0 cb kb T y (stepRun st kj)) (ky : Keep stepRegs u y)
      (y2 : y.gpr stp = BitVec.ofNat 64 j) :
      WP isa (.block [.addi stp stp 1, .addi tmp stp (-40)]) y fun z =>
        KS m0 cb kb T z (stepRun st kj) ∧ z.gpr stp = BitVec.ofNat 64 (j + 1) ∧
          z.gpr tmp = BitVec.ofNat 64 (j + 1) - BitVec.ofNat 64 40 ∧ Keep stepRegs u z := by
    refine wp_addi (imm := 1) (by decide) fun z₁ h₁ => wp_subi (imm := 40) (by decide) fun z₂ h₂ => WP.block_nil ?_
    obtain kz : Keep [stp, tmp] y z₂ := (h₁.keep.trans h₂.keep).mono (by decide)
    refine ⟨hy.update kz (by rw [h₂.mem, h₁.mem]; exact hy.mem) (fun i hi => by rw [h₂.mem, h₁.mem]; exact hy.ex i hi)
      hy.len, ?_, ?_, (ky.trans kz).mono (by decide)⟩
    · rw [h₂.other _ (by decide), h₁.gpr, y2, BitVec.ofNat_add]
    · rw [h₂.gpr, h₁.gpr, y2, BitVec.ofNat_add]
  cases st with
  | extras a b c d =>
    refine WP.mono (postE_ok hx a b c d (exVal kj.xz a b c d) fun i hi => ?_) fun y ⟨hy, ky⟩ =>
      WP.mono (tail y hy ((kuw.trans kx).trans ky |>.mono (by decide))
        (by rw [ky.gpr (by decide), gx _ (by decide), w2])) fun z hz => hz
    · rw [gx _ (by unfold accReg; split <;> decide)]
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega_arith) with rfl | rfl | rfl | rfl
      · exact a0
      · exact a1
      · exact a2
      · exact a3
  | line l store =>
    refine WP.mono (postL_ok hx hok (by rw [gx _ (by decide)]; exact a0) (by rw [gx _ (by decide)]; exact a1)
      (by rw [gx _ (by decide)]; exact a2) (by rw [gx _ (by decide)]; exact a3)
      (by rw [gx _ (by decide)]; exact wout) fun jj e => ?_) fun y ⟨hy, ky⟩ =>
      WP.mono (tail y hy ((kuw.trans kx).trans ky |>.mono (by decide))
        (by rw [ky.gpr (by decide), gx _ (by decide), w2])) fun z hz => hz
    subst e
    obtain hc := hkeys l jj rfl
    obtain hl := ws_length (halfSteps.take j) k0
    rw [hkj] at hl
    obtain hlim : countKeys (halfSteps.take j) < 16 := by
      have := hok; simp only [stepOk, Bool.and_eq_true, decide_eq_true_eq] at this; omega
    exact ⟨by rw [hl, hc, hlen0], by rw [hl, hlen0]; omega_arith⟩

/-! ## A half -/

/-- The registers a half writes. -/
def halfRegs : List Reg := stepRegs ++ [out, hlv]

theorem take_steps_40 : halfSteps.take 40 = halfSteps := by
  rw [List.take_of_length_le (by rw [halfSteps_length])]

theorem tmp_step_ne {j : Nat} (hj : j < 40) :
    (BitVec.ofNat 64 (j + 1) - BitVec.ofNat 64 40 != 0) = !decide (j + 1 = 40) := by
  by_cases he : j + 1 = 40
  · rw [he]; rfl
  · rw [decide_eq_false he]
    have : BitVec.ofNat 64 (j + 1) - BitVec.ofNat 64 40 ≠ 0 := fun e => by
      have := congrArg BitVec.toNat e
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at this
      simp at this; omega_using [hj, he, this]
    simpa using this

theorem half_ok {m0 : Mem} {cb kb T : Addr} {u : State} {k0 : KSt} {hh : Nat} (h : KS m0 cb kb T u k0)
    (hout : u.gpr out = kb + BitVec.ofNat 64 (64 * hh)) (hlen0 : k0.ws.length = 16 * hh) (hhh : hh < 2) :
    WP isa half u fun v => ∃ k, KS m0 cb kb T v k ∧ k.xz = (halfImpl k0.xz).2 ∧
      k.ws = k0.ws ++ (halfImpl k0.xz).1 ∧ v.gpr out = kb + BitVec.ofNat 64 (64 * (hh + 1)) ∧
      v.gpr hlv = u.gpr hlv - 1#64 ∧ Keep halfRegs u v := by
  unfold half
  refine WP.seq (wp_li (imm := 0) (by decide) fun u0 hu0 => WP.block_nil ?_)
  obtain k0u : Keep stepRegs u u0 := hu0.keep.mono (by decide)
  obtain h0 : KS m0 cb kb T u0 (runSteps (halfSteps.take 0) k0) :=
    h.update hu0.keep (by rw [hu0.mem]; exact h.mem) (fun i hi => by rw [hu0.mem]; exact h.ex i hi) h.len
  obtain loop : WP isa (.loop Impl.Cast5.RISCV64.step (.nonzero tmp)) u0
      (fun v => KS m0 cb kb T v (runSteps halfSteps k0) ∧ Keep stepRegs u v) := by
    refine WP.loop (M := isa) (fun m (v : State) => ∃ j, m = 40 - j ∧ j < 40 ∧
      KS m0 cb kb T v (runSteps (halfSteps.take j) k0) ∧ v.gpr stp = BitVec.ofNat 64 j ∧ Keep stepRegs u v)
      ?_ 40 u0 ⟨0, rfl, by decide, h0, hu0.gpr, k0u⟩
    rintro m v ⟨j, rfl, hj, hv, v2, kv⟩
    refine WP.mono (keyStep_ok hj hv v2 (by rw [kv.gpr (by decide), hout]) hlen0 hhh)
      fun w ⟨hw, w2, wt, kw⟩ => ?_
    obtain ev : isa.eval (.nonzero tmp) w = some (!decide (j + 1 = 40)) := by
      rw [eval_nonzero, wt, tmp_step_ne hj]
    by_cases he : j + 1 = 40
    · refine .inl ⟨by rw [ev, decide_eq_true he]; rfl, ?_, (kv.trans kw).mono (by decide)⟩
      rw [he, take_steps_40] at hw; exact hw
    · exact .inr ⟨by rw [ev, decide_eq_false he]; rfl, 40 - (j + 1), by omega_arith, j + 1, rfl,
        by omega_arith, hw, w2, (kv.trans kw).mono (by decide)⟩
  refine WP.seq (WP.mono loop fun v ⟨hv, kv⟩ => ?_)
  refine wp_addi (imm := 64) (by decide) fun v₁ h₁ => wp_subi (imm := 1) (by decide) fun v₂ h₂ => WP.block_nil ?_
  obtain ⟨hx, hw⟩ := runSteps_half k0
  obtain k12 : Keep [out, hlv] v v₂ := (h₁.keep.trans h₂.keep).mono (by decide)
  refine ⟨runSteps halfSteps k0, hv.update k12 (by rw [h₂.mem, h₁.mem]; exact hv.mem)
    (fun i hi => by rw [h₂.mem, h₁.mem]; exact hv.ex i hi) hv.len, hx, hw, ?_, ?_, (kv.trans k12).mono (by decide)⟩
  · rw [h₂.other _ (by decide), h₁.gpr, kv.gpr (by decide), hout, Offset.add_add, Nat.mul_succ]
  · rw [h₂.gpr, h₁.other _ (by decide), kv.gpr (by decide)]

end VG.Proof.Cast5.RISCV64

end

end


/-!
# CAST5 key expansion on RISC-V

`expandKey` saves the callee-saved registers in the working space, rounded
up to a multiple of 8, pads the key with zeros into `x` (§2.5), runs both
halves of §2.4 (`half_ok`) and restores the registers (`key_wp`), as on
PPC64LE (`Proof/Cast5/PPC64LE/Key.lean`).
-/

@[expose] public section

namespace VG.Proof.Cast5.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Cast5 VG.Impl.Cast5.RISCV64 VG.Proof.Cast5

/-! ## The key, padded -/

/-- `x` while the key is copied: the first `j` key bytes, then zeros; `z`
as it was; and only the first 64 bytes of the working space written. -/
structure CInv (m0 : Mem) (key c : Addr) (j : Nat) (m : Mem) : Prop where
  x : ∀ i < 16, m (c + BitVec.ofNat 64 (16 + i)) = if i < j then m0 (key + BitVec.ofNat 64 i) else 0
  z : ∀ i < 16, m (c + BitVec.ofNat 64 (32 + i)) = m0 (c + BitVec.ofNat 64 (32 + i))
  fr : Frame [⟨c, 64⟩] m0 m

theorem zero_dword (m : Mem) (c : Addr) {d e : Nat} (hd : d + 8 ≤ 2 ^ 63) (he : e < 2 ^ 63) :
    (m.writeW (c + BitVec.ofNat 64 d) (0 : BitVec 64)) (c + BitVec.ofNat 64 e) =
      if d ≤ e ∧ e < d + 8 then 0 else m (c + BitVec.ofNat 64 e) := by
  simp only [Mem.writeW]
  rw [byte_write m c _ hd he]
  split
  · simp
  · rfl

theorem zero_ok (s : State) {cb : Addr} (hc : s.gpr wkK = cb) (hal : cb.toNat % 8 = 0)
    (hin : ∀ {off w : Nat}, off + w ≤ 152 → InRegions s.wr (cb + BitVec.ofNat 64 off) w) (key : Addr) :
    WP isa (.block [.li tmp 0, .store .d tmp wkK xOff, .store .d tmp wkK (xOff + 8), .addi dst wkK xOff]) s
      fun u => CInv s.mem key cb 0 u.mem ∧ u.gpr dst = cb + BitVec.ofNat 64 16 ∧ Keep [tmp, dst] s u := by
  obtain i16 := hin (off := 16) (w := 8) (by decide)
  obtain i24 := hin (off := 24) (w := 8) (by decide)
  unfold xOff
  refine wp_li (imm := 0) (by decide) fun u₀ h₀ => ?_
  refine wp_sd (a := cb + BitVec.ofNat 64 16) (by decide) (by rw [h₀.other _ (by decide), hc])
    (Align.al_add hal (by decide) (by decide)) (by rw [h₀.wr]; exact i16) fun u₁ h₁ => ?_
  refine wp_sd (a := cb + BitVec.ofNat 64 24) (by decide)
    (by rw [h₁.gpr, h₀.other _ (by decide), hc]) (Align.al_add hal (by decide) (by decide))
    (by rw [h₁.wr, h₀.wr]; exact i24) fun u₂ h₂ => ?_
  refine wp_addi (imm := 16) (by decide) fun u₃ h₃ => WP.block_nil ?_
  obtain mem : u₃.mem = (s.mem.writeW (cb + BitVec.ofNat 64 16) (0 : BitVec 64)).writeW
      (cb + BitVec.ofNat 64 24) (0 : BitVec 64) := by
    rw [h₃.mem, h₂.mem, h₁.mem, h₁.gpr, h₀.gpr, h₀.mem]; rfl
  refine ⟨⟨fun i hi => ?_, fun i hi => ?_, ?_⟩, by rw [h₃.gpr, h₂.gpr, h₁.gpr, h₀.other _ (by decide), hc], ?_⟩
  · rw [mem, zero_dword _ _ (by decide) (by omega_arith), zero_dword _ _ (by decide) (by omega_arith)]
    repeat' split
    all_goals first | rfl | omega_arith
  · rw [mem, zero_dword _ _ (by decide) (by omega_arith), zero_dword _ _ (by decide) (by omega_arith),
      ite_eq_right (by omega_arith), ite_eq_right (by omega_arith)]
  · rw [mem]
    exact (((Frame.refl _ _).writeW List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))).writeW
      List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide)))
  · refine ⟨fun r hr => ?_, by rw [h₃.rd, h₂.rd, h₁.rd, h₀.rd], by rw [h₃.wr, h₂.wr, h₁.wr, h₀.wr]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [h₃.other _ hr.2, h₂.gpr, h₁.gpr, h₀.other _ hr.1]

theorem copyStep_ok (u : State) {m0 : Mem} {kp cb : Addr} {j : Nat} (hj : j < 16)
    (hI : CInv m0 kp cb j u.mem)
    (h0 : u.gpr key = kp + BitVec.ofNat 64 j) (h3 : u.gpr dst = cb + BitVec.ofNat 64 (16 + j))
    (hr : InRegions (u.rd ++ u.wr) (kp + BitVec.ofNat 64 j) 1)
    (hw : InRegions u.wr (cb + BitVec.ofNat 64 (16 + j)) 1)
    (hk : u.mem (kp + BitVec.ofNat 64 j) = m0 (kp + BitVec.ofNat 64 j)) :
    WP isa (.block copyStep) u fun v =>
      CInv m0 kp cb (j + 1) v.mem ∧ v.gpr key = kp + BitVec.ofNat 64 (j + 1) ∧
      v.gpr dst = cb + BitVec.ofNat 64 (16 + (j + 1)) ∧ v.gpr klen = u.gpr klen - 1#64 ∧
      Keep [tmp, key, dst, klen] u v := by
  unfold copyStep
  refine wp_lbu (by decide) (by rw [h0, BitVec.add_zero]) hr fun u₁ h₁ => ?_
  refine wp_sb (by decide) (by rw [h₁.other _ (by decide), h3, BitVec.add_zero]) (by rw [h₁.wr]; exact hw)
    fun u₂ h₂ => ?_
  refine wp_addi (imm := 1) (by decide) fun u₃ h₃ => wp_addi (imm := 1) (by decide) fun u₄ h₄ =>
    wp_subi (imm := 1) (by decide) fun u₅ h₅ => WP.block_nil ?_
  obtain mem : u₅.mem = u.mem.writeW (cb + BitVec.ofNat 64 (16 + j)) (m0 (kp + BitVec.ofNat 64 j)) := by
    rw [h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.gpr, h₁.mem, hk]
    exact congrArg _ (BitVec.eq_of_getLsbD_eq fun i hi => by simp [hi])
  refine ⟨⟨fun i hi => ?_, fun i hi => ?_, ?_⟩, ?_, ?_, ?_, ⟨fun r hr => ?_, ?_, ?_⟩⟩
  · rw [mem, Mem.writeW, byte_write _ _ _ (by omega_arith) (by omega_arith)]
    by_cases hij : i = j
    · subst hij
      rw [ite_eq_left ⟨Nat.le_refl _, by omega_arith⟩, ite_eq_left (by omega_arith), Nat.sub_self]
      apply BitVec.eq_of_getLsbD_eq; intro k hk
      simp [hk]
    · rw [ite_eq_right (by omega_arith), hI.x i hi]
      by_cases hl : i < j
      · rw [ite_eq_left hl, ite_eq_left (by omega_arith)]
      · rw [ite_eq_right hl, ite_eq_right (by omega_arith)]
  · rw [mem, Mem.writeW, byte_write _ _ _ (by omega_arith) (by omega_arith), ite_eq_right (by omega_arith)]
    exact hI.z i hi
  · rw [mem]; exact hI.fr.writeW List.mem_cons_self _ (Offset.contains_base _ (by omega_arith) (by omega_arith))
  · rw [h₅.other _ (by decide), h₄.other _ (by decide), h₃.gpr, h₂.gpr, h₁.other _ (by decide), h0, Offset.add_add]
  · rw [h₅.other _ (by decide), h₄.gpr, h₃.other _ (by decide), h₂.gpr, h₁.other _ (by decide), h3, Offset.add_add,
      Nat.add_assoc]
  · rw [h₅.gpr, h₄.other _ (by decide), h₃.other _ (by decide), h₂.gpr, h₁.other _ (by decide)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [h₅.other _ hr.2.2.2, h₄.other _ hr.2.2.1, h₃.other _ hr.2.1, h₂.gpr, h₁.other _ hr.1]
  · rw [h₅.rd, h₄.rd, h₃.rd, h₂.rd, h₁.rd]
  · rw [h₅.wr, h₄.wr, h₃.wr, h₂.wr, h₁.wr]

/-! ## The whole function -/

/-- What key expansion may assume: the key readable, the schedule and the
working space writable, the working space apart from both, none wrapping
around, a valid key length; and the table `VG_CAST5_S5678`, readable,
64-byte aligned and apart from the schedule and the working space. -/
structure KeyPre (s : State) : Prop where
  key : (⟨s.gpr .a0, (s.gpr .a1).toNat⟩ : Region) ∈ s.rd ++ s.wr
  kfit : (s.gpr .a0).toNat + (s.gpr .a1).toNat ≤ 2 ^ 64
  sch : (⟨s.gpr .a2, 128⟩ : Region) ∈ s.wr
  Kfit : (s.gpr .a2).toNat + 128 ≤ 2 ^ 64
  scr : (⟨s.gpr .a3, 256⟩ : Region) ∈ s.wr
  sfit : (s.gpr .a3).toNat + 256 ≤ 2 ^ 64
  keyScr : (⟨s.gpr .a0, (s.gpr .a1).toNat⟩ : Region).Disjoint ⟨s.gpr .a3, 256⟩
  schScr : (⟨s.gpr .a2, 128⟩ : Region).Disjoint ⟨s.gpr .a3, 256⟩
  valid : Spec.Cast5.validKey (s.gpr .a1).toNat
  trd : (⟨s.syms s5678Sym, 4096⟩ : Region) ∈ s.rd ++ s.wr
  tal : (s.syms s5678Sym).toNat % 64 = 0
  held : Held s.mem (s.syms s5678Sym) s5678
  tblSch : (⟨s.syms s5678Sym, 4096⟩ : Region).Disjoint ⟨s.gpr .a2, 128⟩
  tblScr : (⟨s.syms s5678Sym, 4096⟩ : Region).Disjoint ⟨s.gpr .a3, 256⟩

/-- What key expansion guarantees. -/
structure KeyPost (s s' : State) : Prop where
  sched : Spec.Cast5.scheduleAt s'.mem (s.gpr .a2) =
    Spec.Cast5.expandKey (Spec.Cast5.bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat)
  saved : ∀ r ∈ saved, s'.gpr r = s.gpr r

theorem ofNat_sub_one64 {a : Nat} (ha : 1 ≤ a) (hb : a < 2 ^ 64) :
    BitVec.ofNat 64 a - 1#64 = BitVec.ofNat 64 (a - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega_arith

theorem key_wp {s : State} (h : KeyPre s) : WP isa expandKey s (KeyPost s) := by
  obtain ⟨n, hnn⟩ : ∃ n, (s.gpr .a1).toNat = n := ⟨_, rfl⟩
  obtain ⟨kp, hkp⟩ : ∃ kp, s.gpr .a0 = kp := ⟨_, rfl⟩
  obtain ⟨kb, hkb⟩ : ∃ kb, s.gpr .a2 = kb := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P, s.gpr .a3 = P := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T, s.syms s5678Sym = T := ⟨_, rfl⟩
  have hkey := h.key; have hkf := h.kfit; have hsch := h.sch; have hKf := h.Kfit; have hscr := h.scr
  have hcf := h.sfit; have dkS := h.keyScr; have dKS := h.schScr; have hn := h.valid
  have htrd := h.trd; have htal := h.tal; have hheld := h.held; have dTK := h.tblSch; have dTS := h.tblScr
  rw [hnn] at hkey hkf dkS hn
  rw [hkp] at hkey hkf dkS
  rw [hkb] at hsch hKf dKS dTK
  rw [hP] at hscr hcf dkS dKS dTS
  rw [hT] at htrd htal hheld dTK dTS
  have hn5 : 5 ≤ n ∧ n ≤ 16 := hn
  have cbT := wbase_toNat hcf
  have hpad := Align.pad_lt P
  have inC : ∀ {off w : Nat}, off + w ≤ 152 → InRegions s.wr (wbase P + BitVec.ofNat 64 off) w :=
    fun hw => wbase_in hscr (by omega_arith)
  have sub88 : Region.Sub ⟨wbase P + BitVec.ofNat 64 64, 88⟩ ⟨P, 256⟩ := wbase_sub _ (by decide)
  unfold expandKey
  apply WP.seq
  refine prologue_ok s wkK (by decide) _ hP hscr fun s₀ sv₀ fr₀ k₀ w₀ t₀ sy₀ => ?_
  have g₀ (q : Reg) (hq : q ∉ [wkK, tbl] := by decide) : s₀.gpr q = s.gpr q := k₀.gpr hq
  -- `x` zeroed.
  refine WP.mono (zero_ok s₀ (cb := wbase P) w₀ (Align.align_al P) (fun hw => by rw [k₀.2.2]; exact inC hw) kp)
    fun s₁ ⟨ci₁, d₁, k₁⟩ => ?_
  obtain ⟨M, hM⟩ : ∃ M, s₀.mem = M := ⟨_, rfl⟩
  rw [hM] at ci₁ sv₀ fr₀
  have dkC : Region.Disjoint ⟨kp, n⟩ ⟨wbase P, 64⟩ := dkS.sub_right (wbase_sub0 P (by decide))
  have hkM (j : Nat) (hj : j < n) : M (kp + BitVec.ofNat 64 j) = s.mem (kp + BitVec.ofNat 64 j) :=
    fr₀.bytes (R := ⟨kp, n⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dkS.sub_right sub88)
      (by show n ≤ 2 ^ 64; omega_arith) hj
  -- The key, copied.
  have hrK : ∀ j < n, InRegions (s.rd ++ s.wr) (kp + BitVec.ofNat 64 j) 1 := fun j hj =>
    ⟨⟨kp, n⟩, hkey, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  have r3₁ : s₁.gpr key = kp := by rw [k₁.gpr (by decide), g₀ key, hkp]
  have r4₁ : s₁.gpr klen = BitVec.ofNat 64 n := by
    rw [k₁.gpr (by decide), g₀ klen, ← hnn, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have rw₁ : s₁.rd = s.rd ∧ s₁.wr = s.wr := ⟨by rw [k₁.2.1, k₀.2.1], by rw [k₁.2.2, k₀.2.2]⟩
  have copy : WP isa (.loop (.block copyStep) (.nonzero klen)) s₁ fun v =>
      CInv M kp (wbase P) n v.mem ∧ Keep [tmp, key, dst, klen] s₁ v := by
    refine WP.loop (M := isa) (fun m (v : State) => ∃ j, m = n - j ∧ j < n ∧
      CInv M kp (wbase P) j v.mem ∧ v.gpr key = kp + BitVec.ofNat 64 j ∧
      v.gpr dst = wbase P + BitVec.ofNat 64 (16 + j) ∧ v.gpr klen = BitVec.ofNat 64 (n - j) ∧
      Keep [tmp, key, dst, klen] s₁ v) ?_ n s₁
      ⟨0, rfl, by omega_arith, ci₁, by rw [r3₁]; simp, by rw [d₁], by rw [r4₁, Nat.sub_zero], Keep.refl _ _⟩
    rintro m v ⟨j, rfl, hj, cv, v0, v3, v1, kv⟩
    have hk : v.mem (kp + BitVec.ofNat 64 j) = M (kp + BitVec.ofNat 64 j) :=
      cv.fr.bytes (R := ⟨kp, n⟩) (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dkC)
        (by show n ≤ 2 ^ 64; omega_arith) hj
    refine WP.mono (copyStep_ok v (by omega_arith) cv v0 v3
      (by rw [kv.2.1, kv.2.2, rw₁.1, rw₁.2]; exact hrK j hj)
      (by rw [kv.2.2, rw₁.2]; exact inC (by omega_arith)) hk) fun w ⟨cw, w0, w3, w1, kw⟩ => ?_
    rw [v1, ofNat_sub_one64 (by omega_arith) (by omega_arith)] at w1
    have ev : isa.eval (.nonzero klen) w = some (BitVec.ofNat 64 (n - j - 1) != 0) := by
      rw [eval_nonzero, w1]
    rw [ofNat_bne_zero (by omega_arith)] at ev
    by_cases he : j + 1 = n
    · refine .inl ⟨by rw [ev, show n - j - 1 = 0 by omega_arith]; rfl, he ▸ cw, (kv.trans kw).mono (by decide)⟩
    · refine .inr ⟨by rw [ev, decide_eq_false (by omega_arith)]; rfl, n - (j + 1), by omega_arith, j + 1, rfl,
        by omega_arith, cw, w0, w3, by rw [w1, Nat.sub_sub], (kv.trans kw).mono (by decide)⟩
  refine WP.seq (WP.mono copy fun v ⟨cv, kv⟩ => ?_)
  have kv' := (k₁.trans kv)
  refine WP.seq (wp_li (imm := 2) (by decide) fun w hw => WP.block_nil ?_)
  have kw := kv'.trans hw.keep
  have gw (q : Reg) (hq : q ∉ [tmp, dst] ++ [tmp, key, dst, klen] ++ [hlv] := by decide) : w.gpr q = s₀.gpr q :=
    kw.gpr hq
  have rdw : w.rd = s.rd := by rw [kw.2.1, k₀.2.1]
  have wrw : w.wr = s.wr := by rw [kw.2.2, k₀.2.2]
  -- The state of key expansion: `x` the padded key, no subkeys yet.
  let st0 : XZ := ⟨fun j => (Spec.Cast5.bytesAt s.mem kp n).getD j 0,
    fun j => M (wbase P + BitVec.ofNat 64 (32 + j))⟩
  have ks0 : KS M (wbase P) kb T w ⟨st0, [],
      fun i => w.mem.readW (wbase P + BitVec.ofNat 64 (extraOff + 4 * i)) 32⟩ :=
    { wk := by rw [gw wkK, w₀]
      mem := ⟨fun a i hi => ?_, fun i hi => absurd hi (Nat.not_lt_zero _), by
        rw [hw.mem]; exact cv.fr.mono (by simp)⟩
      ex := fun _ _ => rfl
      len := Nat.zero_le _
      al := Align.align_al P
      cfit := by omega_arith
      kfit := hKf
      scr := fun hw' => by rw [wrw]; exact inC hw'
      sch := by rw [wrw]; exact hsch
      dKS := dKS.sub_right (wbase_sub0 P (by decide))
      tblR := by rw [gw tbl, t₀, hT]
      trd := by rw [rdw, wrw]; exact htrd
      tal := htal
      held0 := by
        rw [← hM]
        refine held_frame (hM ▸ fr₀) (fun r hr => ?_) (by rw [s5678_len]; decide) hheld
        simp only [List.mem_singleton] at hr; subst hr
        rw [s5678_len]; exact dTS.sub_right sub88
      dTS := dTS.sub_right (wbase_sub0 P (by decide))
      dTK := dTK }
  case refine_1 =>
    rw [hw.mem]
    cases a with
    | x =>
      rw [show off .x + i = 16 + i from rfl, cv.x i hi]
      show _ = (Spec.Cast5.bytesAt s.mem kp n).getD i 0
      rw [Proof.Cast5.bytesAt_getD]
      split
      · rw [hkM i (by omega_arith)]
      · rfl
    | z => exact cv.z i hi
  -- The halves.
  have halves_loop : WP isa (.loop half (.nonzero hlv)) w fun u => ∃ k, KS M (wbase P) kb T u k ∧
      k.xz = (halves st0 2).1 ∧ k.ws = (halves st0 2).2 ∧ Keep halfRegs w u := by
    refine WP.loop (M := isa) (fun m (u : State) => ∃ hh, m = 2 - hh ∧ hh < 2 ∧ ∃ k, KS M (wbase P) kb T u k ∧
      k.xz = (halves st0 hh).1 ∧ k.ws = (halves st0 hh).2 ∧ u.gpr out = kb + BitVec.ofNat 64 (64 * hh) ∧
      u.gpr hlv = BitVec.ofNat 64 (2 - hh) ∧ Keep halfRegs w u) ?_ 2 w
      ⟨0, rfl, by decide, _, ks0, rfl, rfl, by rw [gw out, g₀ out, hkb]; simp, by rw [hw.gpr],
        Keep.refl _ _⟩
    rintro m u ⟨hh, rfl, hhh, k, hk, kx, kws, uout, u3, ku⟩
    refine WP.mono (half_ok hk uout (by rw [kws, halves_length]) hhh)
      fun x ⟨k', hk', kx', kw', xout, x3, kh⟩ => ?_
    have nx : k'.xz = (halves st0 (hh + 1)).1 ∧ k'.ws = (halves st0 (hh + 1)).2 := by
      rw [halves_succ, kx', kw', kx, kws]; exact ⟨rfl, rfl⟩
    rw [u3, ofNat_sub_one64 (by omega_arith) (by omega_arith)] at x3
    have ev : isa.eval (.nonzero hlv) x = some (BitVec.ofNat 64 (2 - hh - 1) != 0) := by
      rw [eval_nonzero, x3]
    rw [ofNat_bne_zero (by omega_arith)] at ev
    by_cases he : hh + 1 = 2
    · exact .inl ⟨by rw [ev, show 2 - hh - 1 = 0 by omega_arith]; rfl, k', hk', he ▸ nx.1, he ▸ nx.2,
        (ku.trans kh).mono (by decide)⟩
    · refine .inr ⟨by rw [ev, decide_eq_false (by omega_arith)]; rfl, 2 - (hh + 1), by omega_arith, hh + 1, rfl,
        by omega_arith, k', hk', nx.1, nx.2, xout, by rw [x3, Nat.sub_sub], (ku.trans kh).mono (by decide)⟩
  refine WP.seq (WP.mono halves_loop fun u ⟨k, hk, kxz, kws, ku⟩ => ?_)
  -- The saved registers, restored.
  have hsv : Spill.Saved (wbase P) s.gpr savedSlots u.mem := by
    refine sv₀.frame hk.mem.fr fun p hp r hr => ?_
    have hl := savedSlots_lt p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)
    · exact (dKS.symm.sub_left (wbase_sub _ (by omega_arith)))
  refine WP.mono (epilogue_ok u wkK (by decide) hk.wk (by rw [ku.2.2, wrw]; exact hscr) hsv)
    fun s' R => ⟨?_, fun r hr => restored_saved R hr⟩
  show Spec.Cast5.scheduleAt s'.mem (s.gpr .a2) = _
  rw [R.mem, hkb, hkp, hnn, scheduleAt_keys hk.mem.keys (by rw [kws, halves_length]), kws,
    Proof.Cast5.expandKey_eq _ st0.z, halves_two]

end VG.Proof.Cast5.RISCV64
