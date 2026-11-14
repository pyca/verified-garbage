module

public import VerifiedGarbage.Proof.Aes.X86.AesNi.Invariant
import VerifiedGarbage.Proof.Aes.X86.AesNi.Tail
import VerifiedGarbage.Proof.Aes.X86.AesNi.Load
import VerifiedGarbage.Proof.Aes.X86.AesNi.Data
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
import VerifiedGarbage.Proof.Aes.X86.AesNi.Restore
import VerifiedGarbage.Proof.Aes.X86.AesNi.CT
public import VerifiedGarbage.Spec.Gcm.Contract
public import VerifiedGarbage.Proof.Gcm.Contract
public import VerifiedGarbage.Proof.Aes.X86.Ctr32
import VerifiedGarbage.Proof.Aes.X86.AesNi.Prologue
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Aes.X86.AesNi.Lit

/-! ### `Aes.X86.AesNi.Loops`, which only this module used -/

section

/-! ### `Aes.X86.AesNi.Body`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.Aes.X86.AesNi
open VG VG.X86 VG.X86.RegUpd
open VG.Proof.Aes.X86 (GPre argRg dstP dstR srcR schP nRounds ctrP datP nBlk scrP scrR)
open VG.Impl.Aes.X86.AesNi (at_ argOp ctrLoad aes xorData regs6 dstReg)
open VG.Spec.Gcm (blockAt inc32)
open VG.Proof.Gcm.X86 (revMask)

/-- Public shape facts for the bulk and tail, evaluated once. -/
theorem regs_shape (rs : List XReg) (h : rs = regs6 ∨ rs = [.xmm0]) :
    rs.Nodup ∧ .xmm6 ∉ rs ∧ .xmm7 ∉ rs ∧ 0 < rs.length := by
  rcases h with rfl | rfl <;> decide

theorem Saved.of_data_frame {to : Bool} {s₀ : State} (hp : GPre to s₀) {m m' : Mem}
    (hs : Saved s₀ m) (hf : Frame [dstR to s₀] m m') : Saved s₀ m' :=
  hs.of_frame hf (fun p h => scratch_contains hp (by have := savedRegs_bound p h; omega_using [this]))
    (by simp only [List.mem_singleton, forall_eq]; exact hp.dDB.symm)

structure Ready (s₀ s : State) (c : Nat) (rs : List XReg) (s' : State) : Prop where
  ks : ∀ k (h : k < rs.length), XBinOp.eval .pshufb (s'.xmm rs[k]) revMask =
    ciph s₀ (Nat.repeat inc32 (c + k) (cb s₀))
  ebx : s'.gpr .ebx = s.gpr .ebx + BitVec.ofNat 32 rs.length
  gpr : ∀ r, r ≠ .eax → r ≠ .ebx → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem encrypt_ok {to : Bool} {s₀ : State} (hp : GPre to s₀) (rs : List XReg)
    (hrs : rs = regs6 ∨ rs = [.xmm0]) {c : Nat} (_hc : c + rs.length ≤ nBlk s₀)
    {s : State} (hI : Inv to s₀ c c s) :
    WP isa (.seq (.block (ctrLoad rs)) (aes rs)) s (Ready s₀ s c rs) := by

  obtain ⟨hnd, h6, h7, hlen⟩ := regs_shape rs hrs
  have hw := hp.fD
  have ep : s.ea (at_ .ebp 16) = addr (scrP s₀) 16 := by
    rw [ea_mk]; simp only [at_, hI.ebp]
  have ea : s.ea (argOp 0) = argAddr s₀ 0 := by
    simp only [State.ea, argOp, at_, argAddr, hI.esp]
  have ha : InRegions (s.rd ++ s.wr) (s.ea (argOp 0)) 4 := by
    rw [ea, hI.rd, hI.wr]
    obtain ⟨r, hr, hc⟩ := hp.rA 0 (.inl (by decide))
    exact ⟨r, List.mem_append_left _ hr, hc⟩
  have harg : s.mem.readW (s.ea (argOp 0)) 32 = schP s₀ := by
    rw [ea]
    exact hI.frame.readW (arg_contains hp (.inl (by decide))) (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.aD
      · exact hp.aB) (by decide)
  have hpfx : InRegions (s.rd ++ s.wr) (s.ea (at_ .ebp 16)) 16 := by
    rw [ep, hI.rd, hI.wr]
    exact inRegions_wr (scratch_in hp (by decide))
  refine WP.seq (WP.mono (ctrLoad_ok rs s hnd h7 hpfx ha)
    fun s₁ ⟨e₁, c₁, a₁, f₁⟩ => ?_)
  have ek : ∀ k (h : k < rs.length), st (s₁.xmm rs[k]) =
      VG.Proof.Aes.ctrState (cb s₀) (c + k) := by
    intro k hk
    rw [e₁ k hk, hI.ebx, ep, hI.scratchPrefix, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact counterLane_state _ _ _ (fun k hk => memory_prefix _ _ hk)
  have hK : Keys (nRounds s₀) (sch s₀) s₁ := GPre.keys hp (by rw [a₁, harg])
    (f₁.rd.trans hI.rd) (f₁.wr.trans hI.wr) (by rw [f₁.mem]; exact hI.frame)
  have ecx₁ : s₁.gpr .ecx = BitVec.ofNat 32 (nRounds s₀) := by
    rw [f₁.gpr .ecx (by decide) (by decide), hI.ecx]
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.mono (aes_ok rs hnd h6 hp.rounds s₁ hK ecx₁)
    fun s₂ ⟨e₂, f₂⟩ => ?_
  have ks : ∀ k (h : k < rs.length), XBinOp.eval .pshufb (s₂.xmm rs[k]) revMask =
      ciph s₀ (Nat.repeat inc32 (c + k) (cb s₀)) := by
    intro k hk
    exact (aesWith_eq _ _ _ _ (by
      rw [e₂ _ (List.getElem_mem hk), ek k hk, ctrState_rev])).symm
  exact ⟨ks, by rw [f₂.gpr, c₁],
    fun r h1 h2 => by rw [f₂.gpr, f₁.gpr r h1 h2],
    f₂.mem.trans f₁.mem, f₂.rd.trans f₁.rd, f₂.wr.trans f₁.wr⟩

/-- Any supported lane group produces the next keystream blocks and XORs
them into the next blocks of the data, stored where the result goes; a
public register-update tail follows. -/
theorem blocks_ok {to : Bool} {s₀ : State} (hp : GPre to s₀) (rs : List XReg)
    (hrs : rs = regs6 ∨ rs = [.xmm0]) (tail : List Instr) {Q : State → Prop}
    {c : Nat} (hc : c + rs.length ≤ nBlk s₀) {s : State} (hI : Inv to s₀ c c s)
    (hQ : ∀ s', Inv to s₀ (c + rs.length) c s' → WP isa (.block tail) s' Q) :
    WP isa (.seq (.block (ctrLoad rs)) (.seq (aes rs) (.block (xorData (dstReg to) rs 0 ++ tail)))) s Q := by
  obtain ⟨hnd, _, h7, hlen⟩ := regs_shape rs hrs
  have hwS := hp.fSrc
  have hwD := hp.fD
  refine WP.seq (WP.mono (WP.seq_iff.mp (encrypt_ok hp rs hrs hc hI)) fun s₁ h => ?_)
  refine WP.seq (WP.mono h fun s₂ hR => ?_)
  have esi₂ : s₂.gpr .esi = datP s₀ + BitVec.ofNat 32 (16 * c) := by
    rw [hR.gpr .esi (by decide) (by decide), hI.esi]
  have dst₂ : s₂.gpr (dstReg to) = dstP to s₀ + BitVec.ofNat 32 (16 * c) := by
    cases to
    · exact esi₂
    · rw [show dstReg true = .edx from rfl, hR.gpr .edx (by decide) (by decide), hI.edx]; rfl
  have wide : ∀ {X : BitVec 32}, X.toNat + 16 * nBlk s₀ ≤ 2 ^ 32 → ∀ k, c + k ≤ nBlk s₀ →
      (X + BitVec.ofNat 32 (16 * c)).setWidth 64 + BitVec.ofNat 64 (16 * (0 + k)) =
        X.setWidth 64 + BitVec.ofNat 64 (16 * (c + k)) := fun {X} hX k hk => by
    change addr X (16 * c) + _ = _
    rw [addr_eq (by omega_using [hc, hlen, hX]), BitVec.add_assoc, ← BitVec.ofNat_add]
    rw [show 16 * c + 16 * (0 + k) = 16 * (c + k) by omega_using []]
  have toNat₂ : ∀ {X : BitVec 32}, X.toNat + 16 * nBlk s₀ ≤ 2 ^ 32 →
      (X + BitVec.ofNat 32 (16 * c)).toNat = X.toNat + 16 * c := fun {X} hX => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hc, hlen, hX]), Nat.mod_eq_of_lt (by omega_using [hc, hlen, hwS])]
  have hsd : s₂.gpr .esi = s₂.gpr (dstReg to) ∨ Region.Disjoint
      ⟨(s₂.gpr .esi).setWidth 64 + BitVec.ofNat 64 (16 * 0), 16 * rs.length⟩
      ⟨(s₂.gpr (dstReg to)).setWidth 64 + BitVec.ofNat 64 (16 * 0), 16 * rs.length⟩ := by
    cases to
    · exact .inl rfl
    · rcases hp.sd with he | hdis
      · have e : datP s₀ = dstP true s₀ := BitVec.eq_of_toNat_eq (by
          have := congrArg BitVec.toNat he
          have h₁ := (datP s₀).isLt
          have h₂ := (dstP true s₀).isLt
          simp only [BitVec.toNat_setWidth] at this
          rwa [Nat.mod_eq_of_lt (by omega_using []), Nat.mod_eq_of_lt (by omega_using [])] at this)
        exact .inl (by rw [esi₂, dst₂, e])
      · refine .inr ?_
        have e₁ := wide hwS 0 (by omega_using [hc])
        have e₂ := wide hwD 0 (by omega_using [hc])
        simp only [Nat.add_zero, Nat.mul_zero] at e₁ e₂
        rw [esi₂, dst₂, Nat.mul_zero, e₁, e₂]
        exact (hdis.sub_left (Offset.sub_base _ (by omega_using [hc]))).sub_right (Offset.sub_base _ (by omega_using [hc]))
  rw [WP.block_append_iff]
  refine WP.mono (xorData_ok (dstReg to) rs 0 s₂ hnd h7 (fun k hk => by
      rw [esi₂, wide hwS k (by omega_using [hc, hk]), hR.rd, hR.wr, hI.rd, hI.wr]
      exact GPre.block_in hp (by omega_using [hc, hk]))
    (fun k hk => by
      rw [dst₂, wide hwD k (by omega_using [hc, hk]), hR.wr, hI.wr]
      exact GPre.block_out hp (by omega_using [hc, hk]))
    (by rw [esi₂, toNat₂ hwS]; omega_using [hc, hwS]) (by rw [dst₂, toNat₂ hwD]; omega_using [hc, hwD]) hsd)
    fun s₃ ⟨b₃, fr₃, g₃, rd₃, wr₃, x₃⟩ => hQ s₃ ?_
  have hm₂ : s₂.mem = s.mem := hR.mem
  rw [hm₂] at b₃ fr₃
  rw [dst₂, Nat.mul_zero, BitVec.add_zero] at fr₃
  have frRun : Frame [⟨tAddr s₀ to c, 16 * rs.length⟩] s.mem s₃.mem := by
    have e : (dstP to s₀ + BitVec.ofNat 32 (16 * c)).setWidth 64 =
        (dstP to s₀).setWidth 64 + BitVec.ofNat 64 (16 * c) := by
      change addr _ _ = _; exact addr_eq (by omega_using [hc, hlen, hwD])
    show Frame [⟨(dstP to s₀).setWidth 64 + BitVec.ofNat 64 (16 * c), _⟩] _ _
    rw [← e]; exact fr₃
  have frData : Frame [dstR to s₀] s.mem s₃.mem := frRun.sub fun r hr => by
    simp only [List.mem_singleton] at hr
    subst hr
    exact ⟨dstR to s₀, List.mem_singleton_self _, run_in hc⟩
  refine ⟨hc, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    rd₃.trans (hR.rd.trans hI.rd),
    wr₃.trans (hR.wr.trans hI.wr), ?_,
    Saved.of_data_frame hp hI.saved frData, ?_, ?_⟩
  · rw [g₃, hR.ebx, hI.ebx, BitVec.add_assoc, ← BitVec.ofNat_add]
  · rw [g₃, hR.gpr .esp (by decide) (by decide), hI.esp]
  · rw [g₃, hR.gpr .ecx (by decide) (by decide), hI.ecx]
  · rw [g₃, hR.gpr .edx (by decide) (by decide), hI.edx]
  · rw [g₃, hR.gpr .ebp (by decide) (by decide), hI.ebp]
  · rw [g₃, esi₂]
  · rw [g₃, hR.gpr .edi (by decide) (by decide), hI.edi]
  · exact hI.frame.trans (frData.mono fun r hr =>
      List.mem_cons.mpr (.inl (List.mem_singleton.mp hr)))
  · rw [frData.readW (scratch_contains hp (by decide)) (by
      intro r hr
      simp only [List.mem_singleton] at hr
      subst hr
      exact hp.dDB.symm) (by decide), hI.scratchPrefix]
  · intro k hk
    have out : ¬ (c ≤ k ∧ k < c + rs.length) →
        blockAt s₃.mem (tAddr s₀ to k) = blockAt s.mem (tAddr s₀ to k) := fun hn =>
      blockAt_frame frRun fun r hr => by
        simp only [List.mem_singleton] at hr
        subst hr
        exact run_sep hp hk hc hn
    by_cases hlo : k < c
    · rw [out (by omega_using [hlo]), hI.blocks k hk]
      simp only [hlo, show k < c + rs.length by omega_using [hlo], ite_true]
    · by_cases hhi : k < c + rs.length
      · obtain ⟨j, rfl⟩ : ∃ j, k = c + j := ⟨k - c, by omega_using [hlo]⟩
        have hj : j < rs.length := by omega_using [hhi]
        have bj := b₃ j hj
        rw [esi₂, dst₂, wide hwS j (by omega_using [hk]), wide hwD j (by omega_using [hk])] at bj
        rw [bj, hI.src hp (by omega_using [hk]) (by omega_using []), hR.ks j hj]
        simp only [hhi, ite_true]
      · rw [out (by omega_using [hhi]), hI.blocks k hk]
        simp only [hlo, hhi, ite_false]

end VG.Proof.Aes.X86.AesNi

end

end


@[expose] public section

namespace VG.Proof.Aes.X86.AesNi
open VG VG.X86
open VG.Proof.Aes.X86 (GPre nBlk)
open VG.Impl.Aes.X86.AesNi (body6 body1)

/-- The six-lane body advances the public loop state by six blocks. -/
theorem body6_ok {to : Bool} {s₀ : State} (hp : GPre to s₀) {c : Nat} (hc : c + 6 ≤ nBlk s₀)
    {s : State} (hI : Inv to s₀ c c s) :
    WP isa (Impl.Aes.X86.AesNi.body6 to) s fun s' =>
      Inv to s₀ (c + 6) (c + 6) s' ∧ s'.cf = some (decide (nBlk s₀ - (c + 6) < 6)) := by
  refine blocks_ok hp Impl.Aes.X86.AesNi.regs6 (.inl rfl) _ hc hI fun s₁ hI₁ => ?_
  change WP isa (.block ((([.alu .add .esi (.imm 96)] : List Instr) ++
    Impl.Aes.X86.AesNi.advTo to 96) ++ (([.alu .sub .edi (.imm 6)] : List Instr) ++
    ([.alu .cmp .edi (.imm 6)] : List Instr)))) s₁ _
  rw [← List.append_assoc]
  rw [WP.block_append_iff]
  exact WP.mono (advance_ok hp hc hI₁) fun s₂ ⟨hI₂, _⟩ =>
    cmpEdi_ok (by decide) (by omega_using [hc]) hI₂

/-- The tail body advances one block and exposes its public zero flag. -/
theorem body1_ok {to : Bool} {s₀ : State} (hp : GPre to s₀) {c : Nat} (hc : c < nBlk s₀)
    {s : State} (hI : Inv to s₀ c c s) :
    WP isa (Impl.Aes.X86.AesNi.body1 to) s fun s' =>
      Inv to s₀ (c + 1) (c + 1) s' ∧ s'.zf = some (decide (nBlk s₀ - (c + 1) = 0)) := by
  refine blocks_ok hp [.xmm0] (.inr rfl) _ hc hI fun s₁ hI₁ => ?_
  exact advance_ok (n := 1) hp (by omega_using [hc]) hI₁


/-- Both public count loops terminate and encrypt every requested block. -/
theorem loops_ok {to : Bool} {s₀ : State} (hp : GPre to s₀) {s : State} (hI : Inv to s₀ 0 0 s)
    (hcf : s.cf = some (decide (nBlk s₀ < 6))) (finish : Prog isa) {Q : State → Prop}
    (hQ : ∀ s', Inv to s₀ (nBlk s₀) (nBlk s₀) s' → WP isa finish s' Q) :
    WP isa (.seq (.ite .b (.block []) (.loop (body6 to) .ae))
      (.seq (.block [.alu .test .edi (.reg .edi)])
        (.seq (.ite .e (.block []) (.loop (body1 to) .ne)) finish))) s Q := by
  refine WP.seq (WP.mono (Q := fun s => ∃ c, nBlk s₀ - c < 6 ∧ Inv to s₀ c c s) ?_ fun s₂ ⟨c, hc, hI₂⟩ => ?_)
  · refine WP.ite (decide (nBlk s₀ < 6)) (by simp [eval, hcf]) (fun h => ?_) (fun h => ?_)
    · exact WP.block_nil ⟨0, by simpa using h, hI⟩
    · let I6 : Nat → State → Prop := fun m s => ∃ c, m = nBlk s₀ - c ∧ c + 6 ≤ nBlk s₀ ∧ Inv to s₀ c c s
      have hstep : ∀ m s, I6 m s → WP isa (body6 to) s (fun s' =>
          (eval .ae s' = some false ∧ ∃ c, nBlk s₀ - c < 6 ∧ Inv to s₀ c c s') ∨
          (eval .ae s' = some true ∧ ∃ m' < m, I6 m' s')) := by
        rintro m s ⟨c, rfl, hc, hI⟩
        refine WP.mono (body6_ok hp hc hI) fun s' ⟨hI', hcf'⟩ => ?_
        by_cases hlt : nBlk s₀ - (c + 6) < 6
        · exact .inl ⟨by simp [eval, hcf', hlt], c + 6, hlt, hI'⟩
        · exact .inr ⟨by simp [eval, hcf', hlt], nBlk s₀ - (c + 6), by omega_using [hc], c + 6, rfl, by omega_using [hlt], hI'⟩
      exact WP.loop (M := isa) I6 hstep (nBlk s₀) s ⟨0, rfl, by simpa using h, hI⟩
  refine WP.seq (WP.mono (testEdi_ok hI₂) fun s₃ ⟨hI₃, hzf⟩ => ?_)
  refine WP.seq (WP.mono (Q := Inv to s₀ (nBlk s₀) (nBlk s₀)) ?_ fun s₄ hI₄ => hQ _ hI₄)
  refine WP.ite (decide (nBlk s₀ - c = 0)) (by simp [eval, hzf]) (fun h => ?_) (fun h => ?_)
  · have : c = nBlk s₀ := by have := hI₃.le; simp at h; omega_using [this, h]
    exact WP.block_nil (this ▸ hI₃)
  · let I1 : Nat → State → Prop := fun m s => ∃ c, m = nBlk s₀ - c ∧ c < nBlk s₀ ∧ Inv to s₀ c c s
    have hstep : ∀ m s, I1 m s → WP isa (body1 to) s (fun s' =>
        (eval .ne s' = some false ∧ Inv to s₀ (nBlk s₀) (nBlk s₀) s') ∨
        (eval .ne s' = some true ∧ ∃ m' < m, I1 m' s')) := by
      rintro m s ⟨c, rfl, hc, hI⟩
      refine WP.mono (body1_ok hp hc hI) fun s' ⟨hI', hzf'⟩ => ?_
      by_cases hlast : nBlk s₀ - (c + 1) = 0
      · have : c + 1 = nBlk s₀ := by omega_using [hc, hlast]
        exact .inl ⟨by simp [eval, hzf', hlast], this ▸ hI'⟩
      · exact .inr ⟨by simp [eval, hzf', hlast], nBlk s₀ - (c + 1), by omega_using [hc], c + 1, rfl, by omega_using [hlast], hI'⟩
    have hlt : c < nBlk s₀ := by have := hI₃.le; simp at h; omega_using [h]
    exact WP.loop (M := isa) I1 hstep (nBlk s₀ - c) s₃ ⟨c, rfl, hlt, hI₃⟩


end VG.Proof.Aes.X86.AesNi

end

end


@[expose] public section

namespace VG.Proof.Aes.X86.AesNi
open VG VG.X86
open VG.Proof.Aes.X86 (CPre GPre dstP ctrPost schP nRounds ctrP datP nBlk ctrSat)
open VG.Spec.Gcm (blockAt blocksAt)

/-- The invariant at exit is exactly the standard's CTR block list, from the
source to the destination. -/
theorem Inv.blocks_end {to : Bool} {s₀ s : State} (hI : Inv to s₀ (nBlk s₀) (nBlk s₀) s) :
    blocksAt s.mem ((dstP to s₀).setWidth 64) (nBlk s₀) =
      Spec.Gcm.ctr32 (ciph s₀) (cb s₀)
        (blocksAt s₀.mem ((datP s₀).setWidth 64) (nBlk s₀)) := by
  apply List.ext_getElem
  · simp [blocksAt, Spec.Gcm.ctr32, Spec.Gcm.keystream]
  · intro k h₁ h₂
    have hk : k < nBlk s₀ := by simpa [blocksAt] using h₁
    have hb := hI.blocks k hk
    simp only [hk, ite_true] at hb
    simp only [blocksAt, Spec.Gcm.ctr32, Spec.Gcm.keystream, List.getElem_map,
      List.getElem_range, List.getElem_zipWith, List.length_map, List.length_range]
    exact hb

/-- `edx` set for the loops: out of place, to the destination. -/
theorem setDst_ok {to : Bool} {s₀ s₁ : State} (hp : GPre to s₀) (hs : Start s₀ s₁) :
    WP isa (.block (Impl.Aes.X86.AesNi.setDst to)) s₁ fun s =>
      Inv to s₀ 0 0 s ∧ s.cf = some (decide (nBlk s₀ < 6)) := by
  cases to
  · exact WP.block_nil ⟨Inv.of_start hp hs (fun _ _ => rfl) hs.edx rfl rfl rfl, hs.cf⟩
  · refine Wp.cons (arg_exec hp hs.toSetup (i := 6) (.inr ⟨rfl, rfl⟩) .edx) (WP.block_nil ⟨?_, ?_⟩)
    · refine Inv.of_start hp hs (fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr) ?_ rfl rfl rfl
      rw [RegUpd.gpr_setReg_self]
      simp only [edxAt, ↓reduceIte, dstP, Nat.mul_zero, BitVec.add_zero]
    · rw [RegUpd.cf_setReg]; exact hs.cf

/-- The counter pointer back in `edx` for `restore`. -/
theorem setCtr_ok {to : Bool} {s₀ s : State} (hp : GPre to s₀) {c p : Nat} (hI : Inv to s₀ c p s) :
    WP isa (.block (Impl.Aes.X86.AesNi.setCtr to)) s fun s' =>
      s'.gpr .edx = ctrP s₀ ∧ (∀ r, r ≠ .edx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
        s'.wr = s.wr := by
  cases to
  · exact WP.block_nil ⟨hI.edx, fun _ _ => rfl, rfl, rfl, rfl⟩
  · refine Wp.cons (arg_exec' hp hI.esp hI.rd hI.frame (fun r hr => ?_) (i := 2) (.inl (by decide)) .edx)
      (WP.block_nil ⟨RegUpd.gpr_setReg_self _ _ _, fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr, rfl, rfl, rfl⟩)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.aD
    · exact hp.aB

/-- Complete functional correctness and cdecl ABI preservation, in place
and out of place. -/
theorem correct {to : Bool} {s₀ : State} (hp : GPre to s₀) :
    WP isa (Impl.Aes.X86.AesNi.ctr32With to) s₀ fun s' =>
      abiPreserved s₀ s' ∧ ctrPost to s₀ s' := by
  unfold Impl.Aes.X86.AesNi.ctr32With
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (prologue_ok s₀ hp) fun s₁ hs => WP.mono (setDst_ok hp hs) fun s₂ ⟨hI, hcf⟩ => ?_
  refine loops_ok hp hI hcf _ fun s₃ hI₃ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (setCtr_ok hp hI₃) fun s₄ ⟨edx₄, g₄, m₄, rd₄, wr₄⟩ => ?_
  refine WP.mono (restore_ok hp (nBlk s₀) (by rw [m₄]; exact hI₃.saved) edx₄
    (by rw [g₄ _ (by decide)]; exact hI₃.ebp) (by rw [g₄ _ (by decide)]; exact hI₃.esp)
    (by rw [rd₄]; exact hI₃.rd) (by rw [wr₄]; exact hI₃.wr) (by rw [m₄]; exact hI₃.frame)
    (by rw [g₄ _ (by decide)]; exact hI₃.ebx)) fun s' ⟨habi, hctr, hdata, _, _⟩ => ?_
  exact ⟨habi, hdata.trans (by rw [m₄]; exact hI₃.blocks_end), hctr⟩

/-- `vg_aes_ctr32_to_aesni` in place. -/
theorem ctr32_correct (s : State) (hs : Proof.Aes.ctr32X86.pre s) :
    ∃ t s', Exec isa Impl.Aes.X86.AesNi.ctr32To s t s' ∧ abiPreserved s s' ∧
      Proof.Aes.ctr32X86.post s s' :=
  have hp := CPre.of hs
  (correct hp.gpre).imp fun _ ⟨s', he, h, h₂, h₃⟩ =>
    ⟨s', he, h, by simpa only [ctrPost, dstP, ↓reduceIte, hp.same] using h₂, h₃⟩

theorem ctr32To_correct (s : State) (hs : Proof.Aes.ctr32ToX86.pre s) :
    ∃ t s', Exec isa Impl.Aes.X86.AesNi.ctr32To s t s' ∧ abiPreserved s s' ∧
      Proof.Aes.ctr32ToX86.post s s' :=
  (correct (GPre.ofTo hs)).imp fun _ ⟨s', he, h⟩ => ⟨s', he, h⟩

end VG.Proof.Aes.X86.AesNi
