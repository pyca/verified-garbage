import VerifiedGarbage.Proof.Aes.X86.AesNi.BlocksMain
import VerifiedGarbage.Proof.Framework.X86.Spill
import VerifiedGarbage.Proof.Aes.X86.ExpandKey
import VerifiedGarbage.Proof.Aes.X86.Ctr32
import VerifiedGarbage.Impl.Aes.X86.AesNi
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Spec.Gcm.Contract
import VerifiedGarbage.Proof.Framework.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.Aes.X86.AesNi.Setup`. -/
section

namespace VG.Proof.Aes.X86.AesNi
open VG VG.X86 VG.X86.RegUpd
open VG.Proof.Aes.X86 (CPre schP nRounds ctrP datP nBlk scrP scrR ctrR argR)
open VG.Impl.Aes.X86.AesNi (at_ argOp savedRegs)

/-- The callee-saved registers are saved in the scratch buffer. -/
abbrev Saved (s₀ : State) (m : Mem) : Prop := Spill.Saved m (addr (scrP s₀)) s₀.gpr savedRegs

theorem savedRegs_bound : ∀ p ∈ savedRegs, p.2 + 4 ≤ 16 := by decide

structure Setup (s₀ s : State) : Prop where
  esp : s.gpr .esp = s₀.gpr .esp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [scrR s₀] s₀.mem s.mem

structure Start (s₀ s : State) : Prop extends VG.Proof.Aes.X86.AesNi.Setup s₀ s where
  eax : s.gpr .eax = schP s₀
  ecx : s.gpr .ecx = VG.X86.arg s₀ 1
  edx : s.gpr .edx = ctrP s₀
  esi : s.gpr .esi = datP s₀
  edi : s.gpr .edi = BitVec.ofNat 32 (nBlk s₀)
  ebp : s.gpr .ebp = scrP s₀
  ebx : s.gpr .ebx = (Spec.Gcm.blockAt s₀.mem ((ctrP s₀).setWidth 64)).extractLsb' 0 32
  saved : VG.Proof.Aes.X86.AesNi.Saved s₀ s.mem
  scratchPrefix : s.mem.readW (addr (scrP s₀) 16) 128 =
    (0 : BitVec 32) ++ (s₀.mem.readW ((ctrP s₀).setWidth 64) 128).extractLsb' 0 96
  cf : s.cf = some (decide (nBlk s₀ < 6))
  zf : s.zf = some (decide (nBlk s₀ = 6))

theorem scratch_contains {s : State} (hp : CPre s) {d n : Nat} (h : d + n ≤ 2048) (hn : 0 < n := by decide) :
    (scrR s).Contains (addr (scrP s) d) n := by
  rw [addr_eq (by have hf := hp.fB; omega)]
  exact Offset.contains_base _ h (by omega)

theorem scratch_in {s : State} (hp : CPre s) {d n : Nat} (h : d + n ≤ 2048) (hn : 0 < n := by decide) :
    InRegions s.wr (addr (scrP s) d) n := by
  refine ⟨scrR s, ?_, VG.Proof.Aes.X86.AesNi.scratch_contains hp h hn⟩
  simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false, or_true]

theorem scratch_sep {s : State} (hp : CPre s) {d n e k : Nat}
    (hd : d + n ≤ 2048) (he : e + k ≤ 2048) (h : d + n ≤ e ∨ e + k ≤ d) (hn : 0 < n := by decide) (hk : 0 < k := by decide) :
    Mem.Sep (addr (scrP s) d) n (addr (scrP s) e) k := by
  have hf := hp.fB
  rw [addr_eq (by omega), addr_eq (by omega)]
  exact Offset.sep _ h (by omega) (by omega)

theorem arg_contains {s : State} (hp : CPre s) {i : Nat} (hi : i < 6) :
    (argR s).Contains (argAddr s i) 4 := by
  have hf := hp.fSp
  change (⟨addr (s.gpr .esp) 4, 24⟩ : Region).Contains (addr (s.gpr .esp) (4 + 4 * i)) 4
  rw [addr_eq (by omega), addr_eq (by omega)]
  rw [show (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 + 4 * i) =
      ((s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4) + BitVec.ofNat 64 (4 * i) by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]]
  exact Offset.contains_base _ (by omega) (by omega)


theorem Setup.setReg {s₀ s : State} (h : VG.Proof.Aes.X86.AesNi.Setup s₀ s) (d : Reg) (v : BitVec 32)
    (hd : .esp ≠ d) : VG.Proof.Aes.X86.AesNi.Setup s₀ (s.setReg d v) :=
  ⟨by rw [gpr_setReg_of_ne _ _ hd]; exact h.esp,
    (rd_setReg _ _ _).trans h.rd, (wr_setReg _ _ _).trans h.wr,
    by rw [mem_setReg]; exact h.frame⟩


theorem ctr_contains {s : State} (hp : CPre s) {d n : Nat} (h : d + n ≤ 16)
    (hn : 0 < n := by decide) : (ctrR s).Contains (addr (ctrP s) d) n := by
  rw [addr_eq (by have hf := hp.fC; omega)]
  exact Offset.contains_base _ h (by omega)


end VG.Proof.Aes.X86.AesNi

end

/- Proofs formerly in `VerifiedGarbage.Proof.Aes.X86.AesNi.Invariant`. -/
section

namespace VG.Proof.Aes.X86.AesNi
open VG VG.X86
open VG.Proof.Aes.X86 (CPre schP nRounds ctrP datP nBlk scrP datR scrR ctrR argR)
open VG.Spec.Gcm (blockAt inc32)

/-- After c encrypted blocks, public data/count registers point at block p.
The prefix and saved callee registers stay in scratch throughout both loops. -/
structure Inv (s₀ : State) (c p : Nat) (s : State) : Prop where
  le : c ≤ nBlk s₀
  ebx : s.gpr .ebx = (cb s₀).extractLsb' 0 32 + BitVec.ofNat 32 c
  esp : s.gpr .esp = s₀.gpr .esp
  ecx : s.gpr .ecx = VG.X86.arg s₀ 1
  edx : s.gpr .edx = ctrP s₀
  ebp : s.gpr .ebp = scrP s₀
  esi : s.gpr .esi = datP s₀ + BitVec.ofNat 32 (16 * p)
  edi : s.gpr .edi = BitVec.ofNat 32 (nBlk s₀ - p)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [datR s₀, scrR s₀] s₀.mem s.mem
  saved : VG.Proof.Aes.X86.AesNi.Saved s₀ s.mem
  scratchPrefix : s.mem.readW (addr (scrP s₀) 16) 128 = (0 : BitVec 32) ++ pfx s₀
  blocks : ∀ k < nBlk s₀,
    VG.Spec.Gcm.blockAt s.mem (VG.Proof.Aes.X86.AesNi.bAddr s₀ k) = if k < c then
      VG.Proof.Aes.X86.AesNi.blk s₀ k ^^^ ciph s₀ (Nat.repeat inc32 k (cb s₀)) else VG.Proof.Aes.X86.AesNi.blk s₀ k

/-- A subrange of the encrypted run lies in the public data region. -/
theorem run_in {s₀ : State} {c n : Nat} (hn : c + n ≤ nBlk s₀) :
    Region.Sub ⟨VG.Proof.Aes.X86.AesNi.bAddr s₀ c, 16 * n⟩ (datR s₀) :=
  Offset.sub_base _ (by omega)

/-- A data block outside the encrypted run cannot overlap that run. -/
theorem run_sep {s₀ : State} (hp : CPre s₀) {c n k : Nat} (hk : k < nBlk s₀)
    (hn : c + n ≤ nBlk s₀) (hout : ¬ (c ≤ k ∧ k < c + n)) :
    Region.Disjoint ⟨VG.Proof.Aes.X86.AesNi.bAddr s₀ k, 16⟩ ⟨VG.Proof.Aes.X86.AesNi.bAddr s₀ c, 16 * n⟩ := by
  have hw := hp.fD
  exact Offset.disjoint _ (by omega) (by omega) (by omega)

/-- Entry setup supplies the loop invariant before any data is encrypted. -/
theorem Inv.of_start {s₀ s : State} (hp : CPre s₀) (hs : VG.Proof.Aes.X86.AesNi.Start s₀ s) :
    VG.Proof.Aes.X86.AesNi.Inv s₀ 0 0 s := by
  refine ⟨Nat.zero_le _, ?_, hs.esp, hs.ecx, hs.edx, hs.ebp, ?_, ?_, hs.rd, hs.wr,
    ?_, hs.saved, hs.scratchPrefix, ?_⟩
  · rw [hs.ebx, BitVec.add_zero]
  · rw [hs.esi, Nat.mul_zero, BitVec.add_zero]
  · simpa only [Nat.sub_zero] using hs.edi
  · exact hs.frame.sub fun r hr => ⟨r, List.mem_cons_of_mem _ hr, fun _ h => h⟩
  · intro k hk
    simp only [Nat.not_lt_zero, ite_false]
    exact blockAt_frame hs.frame (fun r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      exact hp.dDB.sub_left (VG.Proof.Aes.X86.AesNi.run_in (s₀ := s₀) (c := k) (n := 1) (by omega)))

end VG.Proof.Aes.X86.AesNi

end

/- Proofs formerly in `VerifiedGarbage.Proof.Aes.X86.AesNi.Body`. -/
section

namespace VG.Proof.Aes.X86.AesNi
open VG VG.X86 VG.X86.RegUpd
open VG.Proof.Aes.X86 (CPre schP nRounds ctrP datP nBlk scrP datR scrR argR)
open VG.Impl.Aes.X86.AesNi (at_ argOp ctrLoad aes xorData regs6)
open VG.Spec.Gcm (blockAt inc32)
open VG.Proof.Gcm.X86 (revMask)

/-- Public shape facts for the bulk and tail, evaluated once. -/
theorem regs_shape (rs : List XReg) (h : rs = regs6 ∨ rs = [.xmm0]) :
    rs.Nodup ∧ .xmm6 ∉ rs ∧ .xmm7 ∉ rs ∧ 0 < rs.length := by
  rcases h with rfl | rfl <;> decide

theorem Saved.of_data_frame {s₀ : State} (hp : CPre s₀) {m m' : Mem}
    (hs : VG.Proof.Aes.X86.AesNi.Saved s₀ m) (hf : Frame [datR s₀] m m') : VG.Proof.Aes.X86.AesNi.Saved s₀ m' :=
  hs.of_frame hf (fun p h => VG.Proof.Aes.X86.AesNi.scratch_contains hp (by have := VG.Proof.Aes.X86.AesNi.savedRegs_bound p h; omega))
    (by simp only [List.mem_singleton, forall_eq]; exact hp.dDB.symm)

structure Ready (s₀ s : State) (c : Nat) (rs : List XReg) (s' : State) : Prop where
  ks : ∀ k (h : k < rs.length), XBinOp.eval .pshufb (s'.xmm rs[k]) revMask =
    ciph s₀ (Nat.repeat inc32 (c + k) (cb s₀))
  ebx : s'.gpr .ebx = s.gpr .ebx + BitVec.ofNat 32 rs.length
  gpr : ∀ r, r ≠ .eax → r ≠ .ebx → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem encrypt_ok {s₀ : State} (hp : CPre s₀) (rs : List XReg)
    (hrs : rs = regs6 ∨ rs = [.xmm0]) {c : Nat} (_hc : c + rs.length ≤ nBlk s₀)
    {s : State} (hI : VG.Proof.Aes.X86.AesNi.Inv s₀ c c s) :
    WP isa (.seq (.block (ctrLoad rs)) (VG.Impl.Aes.X86.AesNi.aes rs)) s (VG.Proof.Aes.X86.AesNi.Ready s₀ s c rs) := by

  obtain ⟨hnd, h6, h7, hlen⟩ := VG.Proof.Aes.X86.AesNi.regs_shape rs hrs
  have hw := hp.fD
  have ep : s.ea (at_ .ebp 16) = addr (scrP s₀) 16 := by
    rw [ea_mk]; simp only [at_, hI.ebp]
  have ea : s.ea (argOp 0) = argAddr s₀ 0 := by
    simp only [State.ea, argOp, at_, argAddr, hI.esp]
  have ha : InRegions (s.rd ++ s.wr) (s.ea (argOp 0)) 4 := by
    rw [ea, hI.rd, hI.wr]
    exact ⟨argR s₀, by simp [hp.rd], VG.Proof.Aes.X86.AesNi.arg_contains hp (by decide)⟩
  have harg : s.mem.readW (s.ea (argOp 0)) 32 = schP s₀ := by
    rw [ea]
    exact hI.frame.readW (VG.Proof.Aes.X86.AesNi.arg_contains hp (by decide)) (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.aD
      · exact hp.aB) (by decide)
  have hpfx : InRegions (s.rd ++ s.wr) (s.ea (at_ .ebp 16)) 16 := by
    rw [ep, hI.rd, hI.wr]
    exact inRegions_wr (VG.Proof.Aes.X86.AesNi.scratch_in hp (by decide))
  refine WP.seq (WP.mono (ctrLoad_ok rs s hnd h7 hpfx ha)
    fun s₁ ⟨e₁, c₁, a₁, f₁⟩ => ?_)
  have ek : ∀ k (h : k < rs.length), st (s₁.xmm rs[k]) =
      VG.Proof.Aes.ctrState (cb s₀) (c + k) := by
    intro k hk
    rw [e₁ k hk, hI.ebx, ep, hI.scratchPrefix, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact counterLane_state _ _ _ (fun k hk => memory_prefix _ _ hk)
  have hK : Keys (nRounds s₀) (VG.Proof.Aes.X86.AesNi.sch s₀) s₁ := CPre.keys hp (by rw [a₁, harg])
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
exactly those blocks into data; a public register-update tail follows. -/
theorem blocks_ok {s₀ : State} (hp : CPre s₀) (rs : List XReg)
    (hrs : rs = regs6 ∨ rs = [.xmm0]) (tail : List Instr) {Q : State → Prop}
    {c : Nat} (hc : c + rs.length ≤ nBlk s₀) {s : State} (hI : VG.Proof.Aes.X86.AesNi.Inv s₀ c c s)
    (hQ : ∀ s', VG.Proof.Aes.X86.AesNi.Inv s₀ (c + rs.length) c s' → WP isa (.block tail) s' Q) :
    WP isa (.seq (.block (ctrLoad rs)) (.seq (VG.Impl.Aes.X86.AesNi.aes rs) (.block (xorData rs 0 ++ tail)))) s Q := by
  obtain ⟨hnd, _, h7, hlen⟩ := VG.Proof.Aes.X86.AesNi.regs_shape rs hrs
  have hw := hp.fD
  refine WP.seq (WP.mono (WP.seq_iff.mp (VG.Proof.Aes.X86.AesNi.encrypt_ok hp rs hrs hc hI)) fun s₁ h => ?_)
  refine WP.seq (WP.mono h fun s₂ hR => ?_)
  have esi₂ : s₂.gpr .esi = datP s₀ + BitVec.ofNat 32 (16 * c) := by
    rw [hR.gpr .esi (by decide) (by decide), hI.esi]
  have esiNat : (s₂.gpr .esi).toNat = (datP s₀).toNat + 16 * c := by
    rw [esi₂, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have esiWide : (s₂.gpr .esi).setWidth 64 = VG.Proof.Aes.X86.AesNi.bAddr s₀ c := by
    rw [esi₂]
    change addr (datP s₀) (16 * c) = _
    rw [addr_eq (by omega)]
  have addr' : ∀ k, (s₂.gpr .esi).setWidth 64 + BitVec.ofNat 64 (16 * (0 + k)) =
      VG.Proof.Aes.X86.AesNi.bAddr s₀ (c + k) := by
    intro k
    rw [esiWide, VG.Proof.Aes.X86.AesNi.bAddr, VG.Proof.Aes.X86.AesNi.bAddr, BitVec.add_assoc, ← BitVec.ofNat_add]
    rw [show 16 * c + 16 * (0 + k) = 16 * (c + k) by omega]
  rw [WP.block_append_iff]
  refine WP.mono (xorData_ok rs 0 s₂ hnd h7 (fun k hk => by
    rw [addr' k, hR.wr, hI.wr]
    exact CPre.block_out hp (by omega)) (by rw [esiNat]; omega))
    fun s₃ ⟨b₃, fr₃, g₃, rd₃, wr₃, x₃⟩ => hQ s₃ ?_
  have hm₂ : s₂.mem = s.mem := hR.mem
  rw [hm₂] at b₃ fr₃
  rw [esiWide, Nat.mul_zero, BitVec.add_zero] at fr₃
  simp only [addr'] at b₃
  have frData : Frame [datR s₀] s.mem s₃.mem := fr₃.sub fun r hr => by
    simp only [List.mem_singleton] at hr
    subst hr
    exact ⟨datR s₀, List.mem_singleton_self _, VG.Proof.Aes.X86.AesNi.run_in hc⟩
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
  · rw [frData.readW (VG.Proof.Aes.X86.AesNi.scratch_contains hp (by decide)) (by
      intro r hr
      simp only [List.mem_singleton] at hr
      subst hr
      exact hp.dDB.symm) (by decide), hI.scratchPrefix]
  · intro k hk
    have out : ¬ (c ≤ k ∧ k < c + rs.length) →
        VG.Spec.Gcm.blockAt s₃.mem (VG.Proof.Aes.X86.AesNi.bAddr s₀ k) = VG.Spec.Gcm.blockAt s.mem (VG.Proof.Aes.X86.AesNi.bAddr s₀ k) := fun hn =>
      blockAt_frame fr₃ fun r hr => by
        simp only [List.mem_singleton] at hr
        subst hr
        exact VG.Proof.Aes.X86.AesNi.run_sep hp hk hc hn
    by_cases hlo : k < c
    · rw [out (by omega), hI.blocks k hk]
      simp only [hlo, show k < c + rs.length by omega, ite_true]
    · by_cases hhi : k < c + rs.length
      · obtain ⟨j, rfl⟩ : ∃ j, k = c + j := ⟨k - c, by omega⟩
        have hj : j < rs.length := by omega
        rw [b₃ j hj, hI.blocks _ hk, hR.ks j hj]
        simp only [hlo, hhi, ite_false, ite_true]
      · rw [out (by omega), hI.blocks k hk]
        simp only [hlo, hhi, ite_false]

end VG.Proof.Aes.X86.AesNi

end

/- Proofs formerly in `VerifiedGarbage.Proof.Aes.X86.AesNi.Lit`. -/
section

namespace VG.Impl.Aes.X86.AesNi
materialize_code VG.Impl.Aes.X86.AesNi.expandKey
materialize_code VG.Impl.Aes.X86.AesNi.ctr32
end VG.Impl.Aes.X86.AesNi

end

/- Proofs formerly in `VerifiedGarbage.Proof.Aes.X86.AesNi.CT`. -/
section

namespace VG.Proof.Aes.X86.AesNi
open VG.X86

theorem expandKey_ct : ConstantTime isa Proof.Aes.expandKeyX86.pre
    Proof.Aes.expandKeyX86.pub Impl.Aes.X86.AesNi.expandKey :=
  VG.Taint.constantTime (A := sseTaint) Proof.Aes.X86.ekτ₀
    (fun _ _ h₁ h₂ hp => Proof.Aes.X86.ek_agree₀ h₁ h₂ hp) (by taint_decide)

theorem ctr32_ct : ConstantTime isa Proof.Aes.ctr32X86.pre
    Proof.Aes.ctr32X86.pub Impl.Aes.X86.AesNi.ctr32 :=
  VG.Taint.constantTime (A := sseTaint) Proof.Aes.X86.ctrτ₀
    (fun _ _ h₁ h₂ hp => Proof.Aes.X86.ctr_agree₀ h₁ h₂ hp) (by taint_decide)

end VG.Proof.Aes.X86.AesNi

end

/- Proofs formerly in `VerifiedGarbage.Proof.Aes.X86.AesNi.Tail`. -/
section

namespace VG.Proof.Aes.X86.AesNi
open VG VG.X86 VG.X86.RegUpd
open VG.Proof.Aes.X86 (CPre datP nBlk)

/-- Bounded natural counts are zero exactly when their word is zero. -/
theorem beq_ofNat_zero {k : Nat} (hk : k < 2 ^ 32) :
    (BitVec.ofNat 32 k == 0) = decide (k = 0) := by
  by_cases h : k = 0
  · subst h; rfl
  · have he : BitVec.ofNat 32 k ≠ 0 := fun e => h (by
      have he := congrArg BitVec.toNat e
      rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk] at he)
    rw [beq_eq_false_iff_ne.mpr he]
    simp [h]

/-- Public pointer and remaining-count advancement, without changing memory. -/
theorem advance_ok {s₀ : State} (hp : CPre s₀) {c p n : Nat}
    (hn : p + n ≤ nBlk s₀) {s : State} (hI : VG.Proof.Aes.X86.AesNi.Inv s₀ c p s) :
    WP isa (.block [.alu .add .esi (.imm (BitVec.ofNat 32 (16 * n))),
      .alu .sub .edi (.imm (BitVec.ofNat 32 n))]) s fun s' =>
      VG.Proof.Aes.X86.AesNi.Inv s₀ c (p + n) s' ∧ s'.zf = some (decide (nBlk s₀ - (p + n) = 0)) := by
  have hw := hp.fD
  have hsub : BitVec.ofNat 32 (nBlk s₀ - p) - BitVec.ofNat 32 n =
      BitVec.ofNat 32 (nBlk s₀ - (p + n)) := by
    rw [Offset.ofNat_sub_ofNat (by omega)]
    exact congrArg (BitVec.ofNat 32) (by omega)
  have hadd : (datP s₀ + BitVec.ofNat 32 (16 * p)) + BitVec.ofNat 32 (16 * n) =
      datP s₀ + BitVec.ofNat 32 (16 * (p + n)) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact congrArg (fun k => datP s₀ + BitVec.ofNat 32 k) (by omega)
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, runBlock_cons, runStep_some, runBlock_nil,
    isa, exec, execAlu, readSrc, gpr_setReg, gpr_arithFlags, hI.esi, hI.edi,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨{ hI with esi := ?_, edi := ?_ }, ?_⟩
  · simp only [reduceCtorEq, ↓reduceIte, gpr_setReg, gpr_arithFlags,
      ]
    exact hadd
  · simp only [gpr_setReg_self]
    exact hsub
  · rw [zf_setReg, zf_arithFlags, hsub, VG.Proof.Aes.X86.AesNi.beq_ofNat_zero (by omega)]

/-- The bulk-loop branch depends only on the public remaining count. -/
theorem cmpEdi_ok {s₀ : State} {c p n : Nat} (hn : n < 2 ^ 32)
    (hp : p ≤ nBlk s₀) {s : State} (hI : VG.Proof.Aes.X86.AesNi.Inv s₀ c p s) :
    WP isa (.block [.alu .cmp .edi (.imm (BitVec.ofNat 32 n))]) s fun s' =>
      VG.Proof.Aes.X86.AesNi.Inv s₀ c p s' ∧ s'.cf = some (decide (nBlk s₀ - p < n)) := by
  have hnb : nBlk s₀ < 2 ^ 32 := (VG.X86.arg s₀ 4).isLt
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, isa, exec, execAlu,
    readSrc, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨⟨hI.le, hI.ebx, hI.esp, hI.ecx, hI.edx, hI.ebp, hI.esi, hI.edi,
    hI.rd, hI.wr, hI.frame, hI.saved, hI.scratchPrefix, hI.blocks⟩, ?_⟩
  simp only [cf_arithFlags, hI.edi, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt (show nBlk s₀ - p < 2 ^ 32 by omega)]

/-- Zero detection between the bulk and tail loops also uses only the count. -/
theorem testEdi_ok {s₀ : State} {c p : Nat} {s : State} (hI : VG.Proof.Aes.X86.AesNi.Inv s₀ c p s) :
    WP isa (.block [.alu .test .edi (.reg .edi)]) s fun s' =>
      VG.Proof.Aes.X86.AesNi.Inv s₀ c p s' ∧ s'.zf = some (decide (nBlk s₀ - p = 0)) := by
  have hnb : nBlk s₀ < 2 ^ 32 := (VG.X86.arg s₀ 4).isLt
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, isa, exec, execAlu,
    readSrc, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨⟨hI.le, hI.ebx, hI.esp, hI.ecx, hI.edx, hI.ebp, hI.esi, hI.edi,
    hI.rd, hI.wr, hI.frame, hI.saved, hI.scratchPrefix, hI.blocks⟩, ?_⟩
  rw [zf_arithFlags, BitVec.and_self, hI.edi, VG.Proof.Aes.X86.AesNi.beq_ofNat_zero (by omega)]

end VG.Proof.Aes.X86.AesNi

end

/- Proofs formerly in `VerifiedGarbage.Proof.Aes.X86.AesNi.Loops`. -/
section

namespace VG.Proof.Aes.X86.AesNi
open VG VG.X86
open VG.Proof.Aes.X86 (CPre nBlk)
open VG.Impl.Aes.X86.AesNi (body6 body1)

/-- The six-lane body advances the public loop state by six blocks. -/
theorem body6_ok {s₀ : State} (hp : CPre s₀) {c : Nat} (hc : c + 6 ≤ nBlk s₀)
    {s : State} (hI : VG.Proof.Aes.X86.AesNi.Inv s₀ c c s) :
    WP isa Impl.Aes.X86.AesNi.body6 s fun s' =>
      VG.Proof.Aes.X86.AesNi.Inv s₀ (c + 6) (c + 6) s' ∧ s'.cf = some (decide (nBlk s₀ - (c + 6) < 6)) := by
  refine VG.Proof.Aes.X86.AesNi.blocks_ok hp Impl.Aes.X86.AesNi.regs6 (.inl rfl) _ hc hI fun s₁ hI₁ => ?_
  change WP isa (.block (([.alu .add .esi (.imm 96), .alu .sub .edi (.imm 6)] : List Instr) ++
    ([.alu .cmp .edi (.imm 6)] : List Instr))) s₁ _
  rw [WP.block_append_iff]
  exact WP.mono (VG.Proof.Aes.X86.AesNi.advance_ok hp hc hI₁) fun s₂ ⟨hI₂, _⟩ =>
    VG.Proof.Aes.X86.AesNi.cmpEdi_ok (by decide) (by omega) hI₂

/-- The tail body advances one block and exposes its public zero flag. -/
theorem body1_ok {s₀ : State} (hp : CPre s₀) {c : Nat} (hc : c < nBlk s₀)
    {s : State} (hI : VG.Proof.Aes.X86.AesNi.Inv s₀ c c s) :
    WP isa Impl.Aes.X86.AesNi.body1 s fun s' =>
      VG.Proof.Aes.X86.AesNi.Inv s₀ (c + 1) (c + 1) s' ∧ s'.zf = some (decide (nBlk s₀ - (c + 1) = 0)) := by
  refine VG.Proof.Aes.X86.AesNi.blocks_ok hp [.xmm0] (.inr rfl) _ hc hI fun s₁ hI₁ => ?_
  exact VG.Proof.Aes.X86.AesNi.advance_ok (n := 1) hp (by omega) hI₁


/-- Both public count loops terminate and encrypt every requested block. -/
theorem loops_ok {s₀ : State} (hp : CPre s₀) {s : State} (hI : VG.Proof.Aes.X86.AesNi.Inv s₀ 0 0 s)
    (hcf : s.cf = some (decide (nBlk s₀ < 6))) (finish : Prog isa) {Q : State → Prop}
    (hQ : ∀ s', VG.Proof.Aes.X86.AesNi.Inv s₀ (nBlk s₀) (nBlk s₀) s' → WP isa finish s' Q) :
    WP isa (.seq (.ite .b (.block []) (.loop body6 .ae))
      (.seq (.block [.alu .test .edi (.reg .edi)])
        (.seq (.ite .e (.block []) (.loop body1 .ne)) finish))) s Q := by
  refine WP.seq (WP.mono (Q := fun s => ∃ c, nBlk s₀ - c < 6 ∧ VG.Proof.Aes.X86.AesNi.Inv s₀ c c s) ?_ fun s₂ ⟨c, hc, hI₂⟩ => ?_)
  · refine WP.ite (decide (nBlk s₀ < 6)) (by simp [VG.X86.eval, hcf]) (fun h => ?_) (fun h => ?_)
    · exact WP.block_nil ⟨0, by simpa using h, hI⟩
    · let I6 : Nat → State → Prop := fun m s => ∃ c, m = nBlk s₀ - c ∧ c + 6 ≤ nBlk s₀ ∧ VG.Proof.Aes.X86.AesNi.Inv s₀ c c s
      have hstep : ∀ m s, I6 m s → WP isa body6 s (fun s' =>
          (VG.X86.eval .ae s' = some false ∧ ∃ c, nBlk s₀ - c < 6 ∧ VG.Proof.Aes.X86.AesNi.Inv s₀ c c s') ∨
          (VG.X86.eval .ae s' = some true ∧ ∃ m' < m, I6 m' s')) := by
        rintro m s ⟨c, rfl, hc, hI⟩
        refine WP.mono (VG.Proof.Aes.X86.AesNi.body6_ok hp hc hI) fun s' ⟨hI', hcf'⟩ => ?_
        by_cases hlt : nBlk s₀ - (c + 6) < 6
        · exact .inl ⟨by simp [VG.X86.eval, hcf', hlt], c + 6, hlt, hI'⟩
        · exact .inr ⟨by simp [VG.X86.eval, hcf', hlt], nBlk s₀ - (c + 6), by omega, c + 6, rfl, by omega, hI'⟩
      exact WP.loop (M := isa) I6 hstep (nBlk s₀) s ⟨0, rfl, by simpa using h, hI⟩
  refine WP.seq (WP.mono (VG.Proof.Aes.X86.AesNi.testEdi_ok hI₂) fun s₃ ⟨hI₃, hzf⟩ => ?_)
  refine WP.seq (WP.mono (Q := VG.Proof.Aes.X86.AesNi.Inv s₀ (nBlk s₀) (nBlk s₀)) ?_ fun s₄ hI₄ => hQ _ hI₄)
  refine WP.ite (decide (nBlk s₀ - c = 0)) (by simp [VG.X86.eval, hzf]) (fun h => ?_) (fun h => ?_)
  · have : c = nBlk s₀ := by have := hI₃.le; simp at h; omega
    exact WP.block_nil (this ▸ hI₃)
  · let I1 : Nat → State → Prop := fun m s => ∃ c, m = nBlk s₀ - c ∧ c < nBlk s₀ ∧ VG.Proof.Aes.X86.AesNi.Inv s₀ c c s
    have hstep : ∀ m s, I1 m s → WP isa body1 s (fun s' =>
        (VG.X86.eval .ne s' = some false ∧ VG.Proof.Aes.X86.AesNi.Inv s₀ (nBlk s₀) (nBlk s₀) s') ∨
        (VG.X86.eval .ne s' = some true ∧ ∃ m' < m, I1 m' s')) := by
      rintro m s ⟨c, rfl, hc, hI⟩
      refine WP.mono (VG.Proof.Aes.X86.AesNi.body1_ok hp hc hI) fun s' ⟨hI', hzf'⟩ => ?_
      by_cases hlast : nBlk s₀ - (c + 1) = 0
      · have : c + 1 = nBlk s₀ := by omega
        exact .inl ⟨by simp [VG.X86.eval, hzf', hlast], this ▸ hI'⟩
      · exact .inr ⟨by simp [VG.X86.eval, hzf', hlast], nBlk s₀ - (c + 1), by omega, c + 1, rfl, by omega, hI'⟩
    have hlt : c < nBlk s₀ := by have := hI₃.le; simp at h; omega
    exact WP.loop (M := isa) I1 hstep (nBlk s₀ - c) s₃ ⟨c, rfl, hlt, hI₃⟩


end VG.Proof.Aes.X86.AesNi

end

/- Proofs formerly in `VerifiedGarbage.Proof.Aes.X86.AesNi.Prologue`. -/
section

namespace VG.Proof.Aes.X86.AesNi
open VG VG.X86 VG.X86.RegUpd
open VG.Proof.Aes.X86 (CPre schP nRounds ctrP datP nBlk scrP scrR ctrR argR)
open VG.Impl.Aes.X86.AesNi (at_ argOp savedRegs)

theorem arg_exec {s₀ s : State} (hp : CPre s₀) (hs : VG.Proof.Aes.X86.AesNi.Setup s₀ s)
    {i : Nat} (hi : i < 6) (d : Reg) :
    exec (.mov d (.mem (argOp i))) s = some (s.setReg d (arg s₀ i)) := by
  have he : s.ea (argOp i) = argAddr s₀ i := by
    simp only [State.ea, argOp, at_, argAddr, hs.esp]
  have hin : InRegions (s.rd ++ s.wr) (argAddr s₀ i) 4 := by
    refine ⟨argR s₀, ?_, VG.Proof.Aes.X86.AesNi.arg_contains hp hi⟩
    simp only [hs.rd, hp.rd, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false, or_true, true_or]
  have hm : s.mem.readW (argAddr s₀ i) 32 = arg s₀ i :=
    hs.frame.readW (VG.Proof.Aes.X86.AesNi.arg_contains hp hi)
      (fun r hr => by
        simp only [List.mem_singleton] at hr
        subst r; exact hp.aB) (by decide)
  simp only [exec, readSrc, State.load32, he, hin, ite_true, hm, Option.map_some]

/-- The memory after saving the registers. -/
abbrev saveMem (s : State) : Mem := Spill.saveMem s.mem (addr (scrP s)) s.gpr savedRegs

theorem saveMem_saved (s : State) (hp : CPre s) : VG.Proof.Aes.X86.AesNi.Saved s (VG.Proof.Aes.X86.AesNi.saveMem s) :=
  Spill.saveMem_saved_addr _ _ (n := 16) (by decide) (by have := hp.fB; omega)

theorem saveMem_frame (s : State) (hp : CPre s) : Frame [scrR s] s.mem (VG.Proof.Aes.X86.AesNi.saveMem s) :=
  Spill.saveMem_frame List.mem_cons_self _ _ _ _ fun p h =>
    VG.Proof.Aes.X86.AesNi.scratch_contains hp (by have := VG.Proof.Aes.X86.AesNi.savedRegs_bound p h; omega)

def saveHead : List Instr := [.mov .eax (.mem (argOp 5))] ++
  savedRegs.map (fun (r, d) => .store (at_ .eax d) r)

theorem saveHead_ok (s₀ : State) (hp : CPre s₀) :
    WP isa (.block VG.Proof.Aes.X86.AesNi.saveHead) s₀ fun s =>
      VG.Proof.Aes.X86.AesNi.Setup s₀ s ∧ s.gpr .eax = scrP s₀ ∧
      (∀ r, r ≠ .eax → s.gpr r = s₀.gpr r) ∧ s.mem = VG.Proof.Aes.X86.AesNi.saveMem s₀ := by
  have hs : VG.Proof.Aes.X86.AesNi.Setup s₀ s₀ := ⟨rfl, rfl, rfl, Frame.refl _ _⟩
  rw [show VG.Proof.Aes.X86.AesNi.saveHead = .mov .eax (.mem (argOp 5)) :: (Spill.saveCode .eax savedRegs ++ []) from rfl]
  refine Wp.cons (VG.Proof.Aes.X86.AesNi.arg_exec hp hs (i := 5) (by decide) .eax) ?_
  have e : (s₀.setReg .eax (arg s₀ 5)).gpr .eax = scrP s₀ := gpr_setReg_self _ _ _
  refine Spill.save_ok savedRegs (fun p h => by
    rw [e, wr_setReg]; exact VG.Proof.Aes.X86.AesNi.scratch_in hp (by have := VG.Proof.Aes.X86.AesNi.savedRegs_bound p h; omega)) fun s u => ?_
  have hm : s.mem = VG.Proof.Aes.X86.AesNi.saveMem s₀ := by
    rw [u.mem, e, mem_setReg]
    exact Spill.saveMem_congr _ _ (fun _ _ => rfl) fun p h => gpr_setReg_of_ne _ _ (by revert p h; decide)
  refine WP.block_nil ⟨⟨by rw [u.gpr, gpr_setReg_of_ne _ _ (by decide)], by rw [u.rd, rd_setReg],
    by rw [u.wr, wr_setReg], by rw [hm]; exact VG.Proof.Aes.X86.AesNi.saveMem_frame _ hp⟩, by rw [u.gpr, e], fun r hr => ?_, hm⟩
  rw [u.gpr, gpr_setReg_of_ne _ _ hr]


structure Loaded (s₀ s : State) : Prop extends VG.Proof.Aes.X86.AesNi.Setup s₀ s where
  eax : s.gpr .eax = schP s₀
  ecx : s.gpr .ecx = arg s₀ 1
  edx : s.gpr .edx = ctrP s₀
  esi : s.gpr .esi = datP s₀
  edi : s.gpr .edi = arg s₀ 4
  ebp : s.gpr .ebp = scrP s₀

def loadArgs : List Instr :=
  [.mov .ebp (.reg .eax), .mov .eax (.mem (argOp 0)), .mov .ecx (.mem (argOp 1)),
   .mov .edx (.mem (argOp 2)), .mov .esi (.mem (argOp 3)), .mov .edi (.mem (argOp 4))]

theorem loadArgs_ok {s₀ s : State} (hp : CPre s₀) (hs : VG.Proof.Aes.X86.AesNi.Setup s₀ s)
    (hb : s.gpr .eax = scrP s₀) :
    WP isa (.block VG.Proof.Aes.X86.AesNi.loadArgs) s fun s' => VG.Proof.Aes.X86.AesNi.Loaded s₀ s' ∧ s'.mem = s.mem := by
  unfold VG.Proof.Aes.X86.AesNi.loadArgs
  rw [WP.block_cons_iff]
  let s₁ := s.setReg .ebp (s.gpr .eax)
  refine ⟨s₁, rfl, ?_⟩
  have hs₁ := hs.setReg .ebp (s.gpr .eax) (by decide)
  rw [WP.block_cons_iff]
  let s₂ := s₁.setReg .eax (arg s₀ 0)
  refine ⟨s₂, VG.Proof.Aes.X86.AesNi.arg_exec hp hs₁ (i := 0) (by decide) .eax, ?_⟩
  have hs₂ := hs₁.setReg .eax (arg s₀ 0) (by decide)
  rw [WP.block_cons_iff]
  let s₃ := s₂.setReg .ecx (arg s₀ 1)
  refine ⟨s₃, VG.Proof.Aes.X86.AesNi.arg_exec hp hs₂ (i := 1) (by decide) .ecx, ?_⟩
  have hs₃ := hs₂.setReg .ecx (arg s₀ 1) (by decide)
  rw [WP.block_cons_iff]
  let s₄ := s₃.setReg .edx (arg s₀ 2)
  refine ⟨s₄, VG.Proof.Aes.X86.AesNi.arg_exec hp hs₃ (i := 2) (by decide) .edx, ?_⟩
  have hs₄ := hs₃.setReg .edx (arg s₀ 2) (by decide)
  rw [WP.block_cons_iff]
  let s₅ := s₄.setReg .esi (arg s₀ 3)
  refine ⟨s₅, VG.Proof.Aes.X86.AesNi.arg_exec hp hs₄ (i := 3) (by decide) .esi, ?_⟩
  have hs₅ := hs₄.setReg .esi (arg s₀ 3) (by decide)
  rw [WP.block_cons_iff]
  let s₆ := s₅.setReg .edi (arg s₀ 4)
  refine ⟨s₆, VG.Proof.Aes.X86.AesNi.arg_exec hp hs₅ (i := 4) (by decide) .edi, ?_⟩
  refine WP.block_nil ⟨⟨hs₅.setReg .edi (arg s₀ 4) (by decide), ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl⟩
  all_goals
    dsimp only [s₆, s₅, s₄, s₃, s₂, s₁]
    simp only [reduceCtorEq, ↓reduceIte, gpr_setReg]
  exact hb


theorem Saved.writePrefix {s₀ : State} {m : Mem} (hp : CPre s₀) (h : VG.Proof.Aes.X86.AesNi.Saved s₀ m)
    (v : BitVec 128) : VG.Proof.Aes.X86.AesNi.Saved s₀ (m.writeW (addr (scrP s₀) 16) v) :=
  h.writeW_addr (n := 2048) hp.fB (fun p h => by have := VG.Proof.Aes.X86.AesNi.savedRegs_bound p h; omega) (by decide) (by decide) v

def counterSetup : List Instr :=
  [.mov .ebx (.mem (at_ .edx 12)), .bswap .ebx,
   .movdquLoad .xmm7 (at_ .edx 0), .xop (.shift .pslldq .xmm7 4),
   .xop (.shift .psrldq .xmm7 4), .movdquStore (at_ .ebp 16) .xmm7,
   .alu .cmp .edi (.imm 6)]

theorem counterSetup_ok {s₀ s : State} (hp : CPre s₀) (hs : VG.Proof.Aes.X86.AesNi.Loaded s₀ s)
    (saved : VG.Proof.Aes.X86.AesNi.Saved s₀ s.mem) : WP isa (.block VG.Proof.Aes.X86.AesNi.counterSetup) s (VG.Proof.Aes.X86.AesNi.Start s₀) := by
  have hc0 : InRegions (s.rd ++ s.wr) (addr (ctrP s₀) 0) 16 := by
    refine inRegions_wr ⟨ctrR s₀, ?_, VG.Proof.Aes.X86.AesNi.ctr_contains hp (by decide)⟩
    simp only [hs.wr, hp.wr, List.mem_cons, true_or]
  have hc12 : InRegions (s.rd ++ s.wr) (addr (ctrP s₀) 12) 4 := by
    refine inRegions_wr ⟨ctrR s₀, ?_, VG.Proof.Aes.X86.AesNi.ctr_contains hp (by decide)⟩
    simp only [hs.wr, hp.wr, List.mem_cons, true_or]
  have hb16 : InRegions s.wr (addr (scrP s₀) 16) 16 := by
    rw [hs.wr]; exact VG.Proof.Aes.X86.AesNi.scratch_in hp (by decide)
  have ctr0 : s.mem.readW (addr (ctrP s₀) 0) 128 =
      s₀.mem.readW ((ctrP s₀).setWidth 64) 128 := by
    rw [VG.Proof.Aes.X86.addr_zero]
    exact hs.frame.readW (Region.contains_self _ _)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst r; exact hp.dCB) (by decide)
  have ctr12 : s.mem.readW (addr (ctrP s₀) 12) 32 =
      s₀.mem.readW (addr (ctrP s₀) 12) 32 :=
    hs.frame.readW (VG.Proof.Aes.X86.AesNi.ctr_contains hp (by decide))
      (fun r hr => by simp only [List.mem_singleton] at hr; subst r; exact hp.dCB) (by decide)
  dsimp only [addr] at hc0 hc12 hb16 ctr0 ctr12
  apply WP.of_runBlock
  simp (config := {decide := true}) only [VG.Proof.Aes.X86.AesNi.counterSetup, runBlock_cons, runStep_some, runBlock_nil,
    exec, readSrc, State.load32, State.load128, State.store128, XOp.exec, execAlu,
    State.ea, at_, gpr_setReg, gpr_setXmm, xmm_setReg, xmm_setXmm,
    mem_setReg, mem_setXmm, rd_setReg, wr_setReg, wr_setXmm,
    ite_true, ite_false, hs.edx, hs.ebp, hc0, hc12, hb16,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · simp (config := {decide := true}) only [gpr_arithFlags, gpr_setReg, ite_false]; exact hs.esp
    · simp only [rd_arithFlags, rd_setXmm, rd_setReg]; exact hs.rd
    · simp only [wr_arithFlags]; exact hs.wr
    · change Frame [scrR s₀] s₀.mem (s.mem.writeW (addr (scrP s₀) 16)
        (XShiftOp.eval .psrldq (XShiftOp.eval .pslldq (s.mem.readW (addr (ctrP s₀) 0) 128) 4) 4))
      exact hs.frame.writeW (List.mem_singleton_self _) _ (VG.Proof.Aes.X86.AesNi.scratch_contains hp (by decide))
  · simp (config := {decide := true}) only [gpr_arithFlags, gpr_setReg, ite_false]; exact hs.eax
  · simp (config := {decide := true}) only [gpr_arithFlags, gpr_setReg, ite_false]; exact hs.ecx
  · simp (config := {decide := true}) only [gpr_arithFlags, gpr_setReg, ite_false]; exact hs.edx
  · simp (config := {decide := true}) only [gpr_arithFlags, gpr_setReg, ite_false]; exact hs.esi
  · simp (config := {decide := true}) only [gpr_arithFlags, gpr_setReg, ite_false]
    rw [hs.edi, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · simp (config := {decide := true}) only [gpr_arithFlags, gpr_setReg, ite_false]; exact hs.ebp
  · simp (config := {decide := true}) only [gpr_arithFlags, gpr_setReg, ite_true]
    rw [ctr12]; exact VG.Proof.Aes.X86.icb_lo _ hp.fC
  · exact saved.writePrefix hp _
  · change (s.mem.writeW (addr (scrP s₀) 16)
        (XShiftOp.eval .psrldq (XShiftOp.eval .pslldq (s.mem.readW (addr (ctrP s₀) 0) 128) 4) 4)).readW
        (addr (scrP s₀) 16) 128 = _
    rw [Mem.readW_writeW_self _ _ 16 _ (by decide), cache_prefix]
    dsimp only [addr]
    rw [ctr0]
  · simp only [cf_arithFlags, hs.edi]
    rfl
  · simp only [zf_arithFlags, hs.edi]
    apply congrArg some
    simp only [Bool.beq_eq_decide_eq, BitVec.sub_eq_iff_eq_add]
    apply decide_eq_decide.mpr
    constructor
    · intro h; exact congrArg BitVec.toNat h
    · intro h; exact BitVec.eq_of_toNat_eq h

theorem prologue_eq : Impl.Aes.X86.AesNi.prologue = VG.Proof.Aes.X86.AesNi.saveHead ++ VG.Proof.Aes.X86.AesNi.loadArgs ++ VG.Proof.Aes.X86.AesNi.counterSetup := rfl

theorem prologue_ok (s₀ : State) (hp : CPre s₀) :
    WP isa (.block Impl.Aes.X86.AesNi.prologue) s₀ (VG.Proof.Aes.X86.AesNi.Start s₀) := by
  rw [VG.Proof.Aes.X86.AesNi.prologue_eq, List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.Aes.X86.AesNi.saveHead_ok s₀ hp) fun s₁ ⟨h₁, ptr₁, _, mem₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Aes.X86.AesNi.loadArgs_ok hp h₁ ptr₁) fun s₂ ⟨h₂, mem₂⟩ => ?_
  apply VG.Proof.Aes.X86.AesNi.counterSetup_ok hp h₂
  rw [mem₂, mem₁]; exact VG.Proof.Aes.X86.AesNi.saveMem_saved _ hp

end VG.Proof.Aes.X86.AesNi

end

/- Proofs formerly in `VerifiedGarbage.Proof.Aes.X86.AesNi.Restore`. -/
section

namespace VG.Proof.Aes.X86.AesNi
open VG VG.X86 VG.X86.RegUpd
open VG.Proof.Aes.X86 (CPre ctrP datP nBlk scrP ctrR datR scrR retR)
open VG.Impl.Aes.X86.AesNi (at_)

/-- Restoring the saved GPRs does not write memory; only the final numeric
counter word is written, in big-endian byte order. -/
theorem restoreCore_ok {s₀ s : State} (hp : CPre s₀) (saved : VG.Proof.Aes.X86.AesNi.Saved s₀ s.mem)
    (edx : s.gpr .edx = ctrP s₀) (ebp : s.gpr .ebp = scrP s₀)
    (esp : s.gpr .esp = s₀.gpr .esp) (_rd : s.rd = s₀.rd) (wr : s.wr = s₀.wr) :
    WP isa (.block Impl.Aes.X86.AesNi.restore) s fun s' =>
      s'.mem = s.mem.writeW (addr (ctrP s₀) 12) (bswap (s.gpr .ebx)) ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s₀.gpr r) := by
  have hc : InRegions s.wr (addr (ctrP s₀) 12) 4 := by
    refine ⟨ctrR s₀, ?_, VG.Proof.Aes.X86.AesNi.ctr_contains hp (by decide)⟩
    simp only [wr, hp.wr, List.mem_cons, true_or]
  rw [show Impl.Aes.X86.AesNi.restore = .mov .eax (.reg .ebx) :: .bswap .eax :: .store (at_ .edx 12) .eax ::
    (Spill.restoreCode .ebp ([(.ebx, 0), (.esi, 4), (.edi, 8)] ++ [(.ebp, 12)]) ++ []) from rfl]
  refine Wp.wp_mov fun s₁ u₁ => Wp.wp_bswap fun s₂ u₂ => ?_
  refine Wp.wp_stm (by rw [u₂.other _ (by decide), u₁.other _ (by decide), edx])
    (by rw [u₂.wr, u₁.wr]; exact hc) fun s₃ u₃ => ?_
  have hm : s₃.mem = s.mem.writeW (addr (ctrP s₀) 12) (bswap (s.gpr .ebx)) := by
    rw [u₃.mem, u₂.gpr, u₂.mem, u₁.gpr, u₁.mem]
  have e : s₃.gpr .ebp = scrP s₀ := by rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), ebp]
  have sv : VG.Proof.Aes.X86.AesNi.Saved s₀ s₃.mem := by
    rw [hm]
    exact saved.of_readW fun p h => Mem.readW_writeW_sep (hp.dCB.symm.sep
      (VG.Proof.Aes.X86.AesNi.scratch_contains hp (by have := VG.Proof.Aes.X86.AesNi.savedRegs_bound p h; omega)) (VG.Proof.Aes.X86.AesNi.ctr_contains hp (by decide))) (by decide)
  refine Spill.restoreBase_ok _ (by decide) (fun p h => by
      have := VG.Proof.Aes.X86.AesNi.savedRegs_bound p (by revert p h; decide)
      rw [e, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]
      exact inRegions_wr (by rw [wr]; exact VG.Proof.Aes.X86.AesNi.scratch_in hp (by omega)))
    (by rw [e]; exact sv.sub (by decide)) fun s' r' => WP.block_nil ⟨by rw [r'.mem, hm],
        r'.abi (by decide) (by decide) (by rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), esp])⟩

/-- The complete restore preserves the encrypted data and the return slot,
and advances only the low 32 counter bits. -/
theorem restore_ok {s₀ s : State} (hp : CPre s₀) (i : Nat)
    (saved : VG.Proof.Aes.X86.AesNi.Saved s₀ s.mem) (edx : s.gpr .edx = ctrP s₀) (ebp : s.gpr .ebp = scrP s₀)
    (esp : s.gpr .esp = s₀.gpr .esp) (rd : s.rd = s₀.rd) (wr : s.wr = s₀.wr)
    (frame : Frame [datR s₀, scrR s₀] s₀.mem s.mem)
    (low : s.gpr .ebx = (Spec.Gcm.blockAt s₀.mem ((ctrP s₀).setWidth 64)).extractLsb' 0 32 +
      BitVec.ofNat 32 i) :
    WP isa (.block Impl.Aes.X86.AesNi.restore) s fun s' =>
      abiPreserved s₀ s' ∧
      Spec.Gcm.blockAt s'.mem ((ctrP s₀).setWidth 64) =
        Nat.repeat Spec.Gcm.inc32 i (Spec.Gcm.blockAt s₀.mem ((ctrP s₀).setWidth 64)) ∧
      Spec.Gcm.blocksAt s'.mem ((datP s₀).setWidth 64) (nBlk s₀) =
        Spec.Gcm.blocksAt s.mem ((datP s₀).setWidth 64) (nBlk s₀) ∧
      Frame [ctrR s₀, datR s₀, scrR s₀] s₀.mem s'.mem ∧
      Frame [ctrR s₀] s.mem s'.mem := by
  refine WP.mono (VG.Proof.Aes.X86.AesNi.restoreCore_ok hp saved edx ebp esp rd wr) fun s' ⟨mem, regs⟩ => ?_
  have f : Frame [ctrR s₀, datR s₀, scrR s₀] s₀.mem s'.mem := by
    rw [mem]
    exact (frame.mono (fun r hr => List.mem_cons_of_mem _ hr)).writeW
      List.mem_cons_self _ (VG.Proof.Aes.X86.AesNi.ctr_contains hp (by decide))
  have fstore : Frame [ctrR s₀] s.mem s'.mem := by
    rw [mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (VG.Proof.Aes.X86.AesNi.ctr_contains hp (by decide))
  refine ⟨⟨regs, ?_⟩, ?_, ?_, f, fstore⟩
  · exact f.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.rC
      · exact hp.rD
      · exact hp.rB) (by decide)
  · apply VG.Proof.Aes.X86.ctr_after hp.fC (N := BitVec.ofNat 32 i) rfl
    · intro k hk
      rw [mem]
      change (s.mem.write (addr (ctrP s₀) 12) 4 (bswap (s.gpr .ebx))) (addr (ctrP s₀) k) = _
      rw [Mem.write_apply]
      · rw [addr_eq (by have hc := hp.fC; omega)]
        exact frame.bytes (R := ctrR s₀) (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact hp.dCD
          · exact hp.dCB) (by change 16 ≤ 2 ^ 64; decide) (by change k < 16; omega)
      · rw [addr_eq (by have hc := hp.fC; omega), addr_eq (by have hc := hp.fC; omega)]
        exact (Offset.sep_base ((ctrP s₀).setWidth 64) (n := 12) (e := 12) (k := 4)
          (by decide) (by decide)) _ (by rw [Mem.sub_ofNat_toNat _ (by omega)]; exact hk)
    · rw [mem, Mem.readW_writeW_self32, low, ← VG.Proof.Aes.X86.icb_lo _ hp.fC]
  · unfold Spec.Gcm.blocksAt
    refine List.map_congr_left fun j hj => Proof.Gcm.blockAt_congr fun k hk => ?_
    have bound := List.mem_range.mp hj
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact fstore.bytes (R := datR s₀) (fun r hr => by
      simp only [List.mem_singleton] at hr
      subst r; exact hp.dCD.symm) (by change 16 * nBlk s₀ ≤ 2 ^ 64; have hf := hp.fD; omega)
      (by change 16 * j + k < 16 * nBlk s₀; omega)

end VG.Proof.Aes.X86.AesNi

end

/- Proofs formerly in `VerifiedGarbage.Proof.Aes.X86.AesNi.Ctr32`. -/
section

namespace VG.Proof.Aes.X86.AesNi
open VG VG.X86
open VG.Proof.Aes.X86 (CPre schP nRounds ctrP datP nBlk ctrSat)
open VG.Spec.Gcm (blockAt blocksAt)

/-- The invariant at exit is exactly the standard's CTR block list. -/
theorem Inv.blocks_end {s₀ s : State} (hI : VG.Proof.Aes.X86.AesNi.Inv s₀ (nBlk s₀) (nBlk s₀) s) :
    VG.Spec.Gcm.blocksAt s.mem ((datP s₀).setWidth 64) (nBlk s₀) =
      Spec.Gcm.ctr32 (ciph s₀) (cb s₀)
        (VG.Spec.Gcm.blocksAt s₀.mem ((datP s₀).setWidth 64) (nBlk s₀)) := by
  apply List.ext_getElem
  · simp [VG.Spec.Gcm.blocksAt, Spec.Gcm.ctr32, Spec.Gcm.keystream]
  · intro k h₁ h₂
    have hk : k < nBlk s₀ := by simpa [VG.Spec.Gcm.blocksAt] using h₁
    have hb := hI.blocks k hk
    simp only [hk, ite_true] at hb
    simp only [VG.Spec.Gcm.blocksAt, Spec.Gcm.ctr32, Spec.Gcm.keystream, List.getElem_map,
      List.getElem_range, List.getElem_zipWith, List.length_map, List.length_range]
    exact hb

/-- Complete functional correctness and cdecl ABI preservation. -/
theorem correct {s₀ : State} (hp : CPre s₀) :
    WP isa Impl.Aes.X86.AesNi.ctr32 s₀ fun s' =>
      abiPreserved s₀ s' ∧ Proof.Aes.ctr32X86.post s₀ s' := by
  refine WP.seq (WP.mono (VG.Proof.Aes.X86.AesNi.prologue_ok s₀ hp) fun s₁ hs => ?_)
  refine VG.Proof.Aes.X86.AesNi.loops_ok hp (Inv.of_start hp hs) hs.cf _ fun s₂ hI => ?_
  refine WP.mono (VG.Proof.Aes.X86.AesNi.restore_ok hp (nBlk s₀) hI.saved hI.edx hI.ebp hI.esp
    hI.rd hI.wr hI.frame hI.ebx) fun s' ⟨habi, hctr, hdata, _, _⟩ => ?_
  refine ⟨habi, ?_, hctr⟩
  rw [hdata]
  exact hI.blocks_end

theorem ctr32_correct (s : State) (hs : Proof.Aes.ctr32X86.pre s) :
    ∃ t s', Exec isa Impl.Aes.X86.AesNi.ctr32 s t s' ∧ abiPreserved s s' ∧
      Proof.Aes.ctr32X86.post s s' :=
  (VG.Proof.Aes.X86.AesNi.correct (CPre.of hs)).imp fun _ ⟨s', he, h⟩ => ⟨s', he, h⟩

theorem ctr32_verified :
    Verified X86.target Impl.Aes.X86.AesNi.ctr32 (Spec.Gcm.ctr32Contract X86.abi) :=
  Verified.of_correct VG.Proof.Aes.X86.AesNi.ctr32_correct VG.Proof.Aes.X86.AesNi.ctr32_ct (by
    have a0 : arg ctrSat 0 = 0x1000 := by decide
    have a1 : arg ctrSat 1 = 10 := by decide
    have a2 : arg ctrSat 2 = 0x2000 := by decide
    have a3 : arg ctrSat 3 = 0x3000 := by decide
    have a4 : arg ctrSat 4 = 0 := by decide
    have a5 : arg ctrSat 5 = 0x4000 := by decide
    have e : argAddr ctrSat 0 = 0x8004 := by decide
    have esp : ctrSat.gpr .esp = 0x8000 := rfl
    sig_implies [Spec.Gcm.ctr32Contract, Spec.Gcm.ctr32Sig, X86.abi, X86.argSlots,
      X86.argVal, X86.argBytes, Proof.Aes.ctr32X86] [a0, a1, a2, a3, a4, a5, e, esp] using ctrSat)

end VG.Proof.Aes.X86.AesNi

end
