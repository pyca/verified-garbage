import VerifiedGarbage.Proof.Aes.X86.AesNi.Dec
import VerifiedGarbage.Proof.Aes.X86.AesNi.Data
import VerifiedGarbage.Proof.Aes.X86.Common

/-!
# AES-NI on x86 (32-bit): the round keys through `aesimc`

`imcKeys` writes `InvMixColumns` of round keys `1 … nr − 1` to
`scratch + 16 j`, and copies the last round key to `scratch + 224`
(`imcKeys_ok`); `dKeys_of_imc` turns that into what `aesDec` needs.
-/

namespace VG.Proof.Aes.X86.AesNi

open VG VG.X86 VG.X86.RegUpd
open VG.Impl.Aes.X86.AesNi (at_ imcKey copyLast imcKeys)
open VG.Proof.Aes.X86 (reg32 addr_add in_reg reg_contains in_rd part_contains part_sub_reg)
open VG.Spec.Aes (roundKey bytesAt invMixColumns)
open VG.Proof.Aes (rkState)

theorem ea_at (s : State) (b : Reg) (d : Nat) : s.ea (at_ b d) = addr (s.gpr b) d := rfl

/-- Where the round keys go through `aesimc`: the key schedule at `eax`
(240 bytes, readable) and the scratch buffer at `edx` (2048 bytes,
writable), apart. -/
structure ImcSetup (s₀ : State) : Prop where
  sch : reg32 (s₀.gpr .eax) 240 ∈ s₀.rd ++ s₀.wr
  scr : reg32 (s₀.gpr .edx) 2048 ∈ s₀.wr
  fitS : (s₀.gpr .eax).toNat + 240 ≤ 2 ^ 32
  fitB : (s₀.gpr .edx).toNat + 2048 ≤ 2 ^ 32
  sep : (reg32 (s₀.gpr .eax) 240).Disjoint (reg32 (s₀.gpr .edx) 2048)

/-- After writing the round keys `S` through `aesimc` to the scratch buffer,
from `s₀`. -/
structure ImcInv (s₀ : State) (S : List Nat) (s : State) : Prop where
  gpr : s.gpr = s₀.gpr
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  xmm : ∀ r, r ≠ .xmm6 → s.xmm r = s₀.xmm r
  frame : Frame [⟨addr (s₀.gpr .edx) 16, 224⟩] s₀.mem s.mem
  le : ∀ j ∈ S, j ≤ 13
  keys : ∀ j ∈ S, s.mem.readW (addr (s₀.gpr .edx) (16 * j)) 128 =
    aesInvMixColumns (s₀.mem.readW (addr (s₀.gpr .eax) (16 * j)) 128)

theorem ImcInv.refl (s₀ : State) : ImcInv s₀ [] s₀ :=
  ⟨rfl, rfl, rfl, fun _ _ => rfl, Frame.refl _ _, fun _ h => absurd h List.not_mem_nil,
    fun _ h => absurd h List.not_mem_nil⟩

theorem ImcInv.of_frame {s₀ s s' : State} {S : List Nat} (h : ImcInv s₀ S s) (hf : XFrame [] s s') :
    ImcInv s₀ S s' :=
  ⟨hf.gpr.trans h.gpr, hf.rd.trans h.rd, hf.wr.trans h.wr,
    fun r hr => (hf.xmm r (by simp)).trans (h.xmm r hr), by rw [hf.mem]; exact h.frame, h.le,
    by rw [hf.mem]; exact h.keys⟩

section
variable {s₀ : State} (hs : ImcSetup s₀)
include hs

theorem ImcSetup.schIn {j : Nat} (hj : j ≤ 14) :
    InRegions (s₀.rd ++ s₀.wr) (addr (s₀.gpr .eax) (16 * j)) 16 :=
  in_reg hs.sch hs.fitS (by omega) (by decide)

theorem ImcSetup.scrIn {o : Nat} (ho : o + 16 ≤ 240) :
    InRegions s₀.wr (addr (s₀.gpr .edx) o) 16 :=
  in_reg hs.scr hs.fitB (by omega) (by decide)

/-- Writes to bytes 16 … 239 of the scratch buffer leave the schedule. -/
theorem ImcSetup.sched {m m' : Mem} (hf : Frame [⟨addr (s₀.gpr .edx) 16, 224⟩] m m') {j : Nat} (hj : j ≤ 14) :
    m'.readW (addr (s₀.gpr .eax) (16 * j)) 128 = m.readW (addr (s₀.gpr .eax) (16 * j)) 128 :=
  hf.readW (reg_contains hs.fitS (by omega) (by decide))
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hs.sep.sub_right (part_sub_reg hs.fitB (by omega))) (by decide)

theorem ImcSetup.frameIn {m m' : Mem} {o : Nat} (ho₁ : 16 ≤ o) (ho : o + 16 ≤ 240) (v : BitVec 128)
    (hf : Frame [⟨addr (s₀.gpr .edx) 16, 224⟩] m m') :
    Frame [⟨addr (s₀.gpr .edx) 16, 224⟩] m (m'.writeW (addr (s₀.gpr .edx) o) v) :=
  hf.writeW (List.mem_singleton_self _) _
    (part_contains hs.fitB (by omega) ho₁ (by omega) (by decide))

theorem imcKey_ok {S : List Nat} {s : State} (hI : ImcInv s₀ S s) {j : Nat} (hj1 : 1 ≤ j) (hj : j ≤ 13) :
    WP isa (.block (imcKey j)) s (ImcInv s₀ (j :: S)) := by
  have hin : InRegions (s.rd ++ s.wr) (s.ea (at_ .eax (16 * j))) 16 := by
    rw [hI.rd, hI.wr, ea_at, hI.gpr]; exact hs.schIn (by omega)
  have hout : InRegions s.wr (s.ea (at_ .edx (16 * j))) 16 := by
    rw [hI.wr, ea_at, hI.gpr]; exact hs.scrIn (by omega)
  have ek : s.ea (at_ .eax (16 * j)) = addr (s₀.gpr .eax) (16 * j) := by rw [ea_at, hI.gpr]
  have es : s.ea (at_ .edx (16 * j)) = addr (s₀.gpr .edx) (16 * j) := by rw [ea_at, hI.gpr]
  apply WP.of_runBlock
  simp only [imcKey, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
    isa, State.load128, State.store128, ea_setXmm, gpr_setXmm, mem_setXmm, rd_setXmm, wr_setXmm,
    xmm_setXmm, hin, hout, XBinOp.eval, Option.map_some, Option.some.injEq, exists_eq_left']
  rw [ek, es]
  refine ⟨hI.gpr, hI.rd, hI.wr, fun r hr => by simp only [xmm_setXmm, hr, ite_false]; exact hI.xmm r hr, ?_, fun j' hj' => ?_,
    fun j' hj' => ?_⟩
  · exact hs.frameIn (by omega) (by omega) _ hI.frame
  · rcases List.mem_cons.mp hj' with rfl | hj'
    · exact hj
    · exact hI.le j' hj'
  · rw [hs.sched hI.frame (by omega)]
    rcases List.mem_cons.mp hj' with rfl | hj'
    · rw [Mem.readW_writeW_self _ _ 16 _ (by decide)]
    · by_cases he : j' = j
      · subst he; rw [Mem.readW_writeW_self _ _ 16 _ (by decide)]
      · have h13 := hI.le j' hj'
        rw [Mem.readW_writeW_sep (by
            rw [addr_eq (by have := hs.fitB; omega), addr_eq (by have := hs.fitB; omega)]
            exact Offset.sep _ (by omega) (by omega) (by omega)) (by decide), hI.keys j' hj']

/-- Some round keys through `aesimc`, those of `js`. -/
theorem imcRun_ok (js : List Nat) (hjs : ∀ j ∈ js, 1 ≤ j ∧ j ≤ 13) {S : List Nat} {s : State}
    (hI : ImcInv s₀ S s) :
    WP isa (.block (js.flatMap imcKey)) s fun s' => ∃ S', ImcInv s₀ S' s' ∧ ∀ j, j ∈ js ∨ j ∈ S → j ∈ S' := by
  induction js generalizing S s with
  | nil => exact WP.block_nil ⟨S, hI, fun j h => by simpa using h⟩
  | cons j js ih =>
    rw [List.flatMap_cons, WP.block_append_iff]
    refine WP.mono (imcKey_ok hs hI (hjs j (by simp)).1 (hjs j (by simp)).2) fun s₁ hI₁ => ?_
    refine WP.mono (ih (fun j' hj' => hjs j' (by simp [hj'])) hI₁) fun s' ⟨S', hI', hS'⟩ =>
      ⟨S', hI', fun j' hj' => hS' j' ?_⟩
    rcases hj' with hj' | hj'
    · rcases List.mem_cons.mp hj' with rfl | hj'
      · exact .inr (by simp)
      · exact .inl hj'
    · exact .inr (by simp [hj'])

/-- The last round key, `nr`, copied to `scratch + 224`. -/
theorem copyLast_ok {S : List Nat} {s : State} (hI : ImcInv s₀ S s) {nr : Nat} (hnr : nr ≤ 14) :
    WP isa (.block (copyLast nr)) s fun s' => ImcInv s₀ S s' ∧
      s'.mem.readW (addr (s₀.gpr .edx) 224) 128 = s₀.mem.readW (addr (s₀.gpr .eax) (16 * nr)) 128 := by
  have hin : InRegions (s.rd ++ s.wr) (s.ea (at_ .eax (16 * nr))) 16 := by
    rw [hI.rd, hI.wr, ea_at, hI.gpr]; exact hs.schIn hnr
  have hout : InRegions s.wr (s.ea (at_ .edx 224)) 16 := by
    rw [hI.wr, ea_at, hI.gpr]; exact hs.scrIn (by omega)
  have ek : s.ea (at_ .eax (16 * nr)) = addr (s₀.gpr .eax) (16 * nr) := by rw [ea_at, hI.gpr]
  have es : s.ea (at_ .edx 224) = addr (s₀.gpr .edx) 224 := by rw [ea_at, hI.gpr]
  apply WP.of_runBlock
  simp only [copyLast, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec,
    isa, State.load128, State.store128, ea_setXmm, gpr_setXmm, mem_setXmm, rd_setXmm, wr_setXmm,
    xmm_setXmm, hin, hout, Option.map_some, Option.some.injEq, exists_eq_left']
  rw [ek, es]
  refine ⟨⟨hI.gpr, hI.rd, hI.wr, fun r hr => by simp only [xmm_setXmm, hr, ite_false]; exact hI.xmm r hr, hs.frameIn (by omega) (by omega) _ hI.frame,
    hI.le, fun j hj => ?_⟩, ?_⟩
  · have h13 := hI.le j hj
    rw [Mem.readW_writeW_sep (by
        rw [addr_eq (by have := hs.fitB; omega), addr_eq (by have := hs.fitB; omega)]
        exact Offset.sep _ (by omega) (by omega) (by omega)) (by decide), hI.keys j hj]
  · rw [Mem.readW_writeW_self _ _ 16 _ (by decide), hs.sched hI.frame hnr]

omit hs in
theorem cmpEcx_imc {S : List Nat} {s : State} (hI : ImcInv s₀ S s) (c : BitVec 32) :
    WP isa (.block [.alu .cmp .ecx (.imm c)]) s fun s' =>
      s'.zf = some (s₀.gpr .ecx - c == 0) ∧ ImcInv s₀ S s' :=
  WP.mono (cmpEcx_ok s c) fun _ ⟨hz, hf⟩ => ⟨by rw [hz, hI.gpr], hI.of_frame hf⟩

/-- What `imcKeys` leaves. -/
def ImcDone (s₀ : State) (nr : Nat) (s : State) : Prop :=
  ∃ S, ImcInv s₀ S s ∧ (∀ j, 1 ≤ j → j < nr → j ∈ S) ∧
    s.mem.readW (addr (s₀.gpr .edx) 224) 128 = s₀.mem.readW (addr (s₀.gpr .eax) (16 * nr)) 128

theorem imcKeys_ok {nr : Nat} (hnr : nr = 10 ∨ nr = 12 ∨ nr = 14)
    (hc : s₀.gpr .ecx = BitVec.ofNat 32 nr) : WP isa imcKeys s₀ (ImcDone s₀ nr) := by
  have run := fun js (hjs : ∀ j ∈ js, 1 ≤ j ∧ j ≤ 13) {S s} (hI : ImcInv s₀ S s) => imcRun_ok hs js hjs hI
  refine WP.seq ?_
  rw [WP.block_append_iff, show ((List.range 9).flatMap fun j => imcKey (j + 1)) =
    ((List.range 9).map (· + 1)).flatMap imcKey by simp [List.flatMap_map]]
  refine WP.mono (run _ (by decide) (ImcInv.refl s₀)) fun s₁ ⟨S₁, hI₁, hS₁⟩ => ?_
  have h9 : ∀ j, 1 ≤ j → j ≤ 9 → j ∈ S₁ := fun j h1 h2 => hS₁ j (.inl (by
    simp only [List.mem_map, List.mem_range]; exact ⟨j - 1, by omega, by omega⟩))
  refine WP.mono (cmpEcx_imc hI₁ 10) fun s₂ ⟨hz₂, hI₂⟩ => ?_
  rw [hc] at hz₂
  rcases hnr with rfl | rfl | rfl
  · refine WP.ite true (by simp [eval, hz₂]) (fun _ => ?_) (fun h => absurd h (by decide))
    exact WP.mono (copyLast_ok hs hI₂ (by decide)) fun s₃ ⟨hI₃, hl₃⟩ =>
      ⟨S₁, hI₃, fun j h1 h2 => h9 j h1 (by omega), hl₃⟩
  all_goals
    refine WP.ite false (by simp [eval, hz₂]) (fun h => absurd h (by decide)) fun _ => ?_
    refine WP.seq ?_
    rw [WP.block_append_iff, show imcKey 10 ++ imcKey 11 = [10, 11].flatMap imcKey by simp]
    refine WP.mono (run _ (by decide) hI₂) fun s₃ ⟨S₃, hI₃, hS₃⟩ => ?_
    have h11 : ∀ j, 1 ≤ j → j ≤ 11 → j ∈ S₃ := fun j h1 h2 => hS₃ j (by
      by_cases h : j ≤ 9
      · exact .inr (h9 j h1 h)
      · exact .inl (by simp; omega))
    refine WP.mono (cmpEcx_imc hI₃ 12) fun s₄ ⟨hz₄, hI₄⟩ => ?_
    rw [hc] at hz₄
  · refine WP.ite true (by simp [eval, hz₄]) (fun _ => ?_) (fun h => absurd h (by decide))
    exact WP.mono (copyLast_ok hs hI₄ (by decide)) fun s₅ ⟨hI₅, hl₅⟩ =>
      ⟨S₃, hI₅, fun j h1 h2 => h11 j h1 (by omega), hl₅⟩
  · refine WP.ite false (by simp [eval, hz₄]) (fun h => absurd h (by decide)) fun _ => ?_
    rw [show imcKey 12 ++ imcKey 13 ++ copyLast 14 = [12, 13].flatMap imcKey ++ copyLast 14 by simp,
      WP.block_append_iff]
    refine WP.mono (run _ (by decide) hI₄) fun s₅ ⟨S₅, hI₅, hS₅⟩ => ?_
    exact WP.mono (copyLast_ok hs hI₅ (by decide)) fun s₆ ⟨hI₆, hl₆⟩ =>
      ⟨S₅, hI₆, fun j h1 h2 => hS₅ j (by
        by_cases h : j ≤ 11
        · exact .inr (h11 j h1 h)
        · exact .inl (by simp; omega)), hl₆⟩

/-- The round keys through `aesimc`, as decryption needs them. -/
theorem dKeys_of_imc {s : State} {nr : Nat} {w : List Byte} (hK : Keys nr w s₀)
    (hd : ImcDone s₀ nr s) : DKeys nr w s := by
  obtain ⟨S, hI, hS, hl⟩ := hd
  have hle := hK.le
  have ek : ∀ j, s.ea (at_ .eax (16 * j)) = s₀.ea (at_ .eax (16 * j)) := fun j => by
    rw [ea_at, ea_at, hI.gpr]
  have hK' : Keys nr w s := ⟨hle, fun j hj => by rw [ek, hI.rd, hI.wr]; exact hK.keys j hj,
    fun j hj => by
      rw [ek, ea_at, hs.sched hI.frame (by omega), ← ea_at]; exact hK.bytes j hj⟩
  refine ⟨hK', fun j h1 h2 => ⟨?_, ?_⟩, ⟨?_, fun i hi => ?_⟩⟩
  · rw [hI.rd, hI.wr, ea_at, hI.gpr]; exact in_rd (hs.scrIn (by omega))
  · rw [ea_at, hI.gpr, hI.keys j (hS j h1 h2), st_aesimc]
    refine congrArg invMixColumns ?_
    apply st_ext; intro i hi
    rw [getD_st _ hi, ← ea_at, hK.bytes j (by omega) i hi]
    simp [rkState, Vector.getD, hi]
  · rw [hI.rd, hI.wr, ea_at, hI.gpr]; exact in_rd (hs.scrIn (by omega))
  · rw [ea_at, hI.gpr, hl, ← ea_at]; exact hK.bytes nr (Nat.le_refl _) i hi

end

end VG.Proof.Aes.X86.AesNi
