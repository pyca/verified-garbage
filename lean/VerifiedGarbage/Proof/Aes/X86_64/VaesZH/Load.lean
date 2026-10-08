import VerifiedGarbage.Proof.Aes.X86_64.VaesZH.Rounds

/-! # Loading the AES schedule into the high registers -/

namespace VG.Proof.Aes.X86_64.VaesZH

open VG.X86_64
open VG.Impl.Aes.X86_64.VaesZH
open VG.Impl.Aes.X86_64.AesNi (at_)
open VG.Proof.Aes.X86_64.AesNi (ea_at)

abbrev MemKeys := VG.Proof.Aes.X86_64.AesNi.Keys

def Loaded (n : Nat) (s : State) : Prop := ∀ j < n, ∀ l < 4,
  s.zlaneH (keyReg j) l = s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (16 * j)) 128

theorem Loaded.keep {n : Nat} {s t : State} {rs : List XReg} (h : Loaded n s)
    (f : KFrame rs s t) : Loaded n t := fun j hj l hl => by
  rw [f.toHKeep.lane, f.mem, f.gpr]; exact h j hj l hl

theorem keyReg_inj : ∀ i < 14, ∀ j < 14, keyReg i = keyReg j → i = j := by decide

theorem keyReg_ne_last : ∀ i < 14, keyReg i ≠ .xmm31 := by decide

theorem loadNext_ok {nr : Nat} {w : List Byte} (j : Nat) (s : State)
    (hk : MemKeys nr w s) (hj : j ≤ nr) (h14 : j < 14) (hL : Loaded j s) :
    WP isa (.block [loadKey j]) s fun t => Loaded (j + 1) t ∧ MemKeys nr w t ∧ ZFrame [] s t := by
  let a := s.gpr .rdi + BitVec.ofNat 64 (16 * j)
  let v := s.mem.readW a 128
  have hin : InRegions (s.rd ++ s.wr) (s.ea (at_ .rdi (16 * j))) 16 := by
    rw [ea_at]; exact hk.keys j hj
  rw [WP.block_cons_iff]
  refine ⟨s.setZH (keyReg j) v v v v,
    by simp only [isa, exec, loadKey, State.load128, hin, ite_true, Option.map_some];
       congr 1 <;> simp only [v, a, ea_at, BitVec.ofInt_natCast], WP.block_nil ?_⟩
  have hf := s.setZH_zframe (keyReg j) v v v v
  refine ⟨fun i hi l hl => ?_, VaesZ.ZFrame.of_keys hk hf, hf⟩
  rw [State.zlaneH_setZH _ _ _ _ _ _ _ hl]
  by_cases hij : i = j
  · subst hij
    simp only [ite_true, pick4]
    split <;> (try split) <;> (try split) <;> rfl
  · have hreg : keyReg i ≠ keyReg j := fun he => hij (keyReg_inj i (by omega) j h14 he)
    simp only [hreg, ite_false]
    exact hL i (by omega) l hl

theorem loadPrefix_ok {nr : Nat} {w : List Byte} (n : Nat) (s : State)
    (hk : MemKeys nr w s) (hn : n ≤ nr) (h14 : n ≤ 14) :
    WP isa (.block ((List.range n).map loadKey)) s fun t =>
      Loaded n t ∧ MemKeys nr w t ∧ ZFrame [] s t := by
  induction n with
  | zero => exact WP.block_nil ⟨fun _ h => by omega, hk, ZFrame.refl _ _⟩
  | succ n ih =>
    rw [List.range_succ, List.map_append, WP.block_append_iff]
    refine WP.mono (ih (by omega) (by omega)) fun t ⟨hL, hk', hf⟩ => ?_
    exact WP.mono (loadNext_ok n t hk' (by omega) (by omega) hL)
      fun u ⟨hL', hk'', hf'⟩ => ⟨hL', hk'', hf.trans hf'⟩

theorem loadTwo_ok {nr : Nat} {w : List Byte} (j : Nat) (s : State)
    (hk : MemKeys nr w s) (hj : j + 2 ≤ nr) (h14 : j + 2 ≤ 14) (hL : Loaded j s) :
    WP isa (.block [loadKey j, loadKey (j + 1)]) s fun t =>
      Loaded (j + 2) t ∧ MemKeys nr w t ∧ ZFrame [] s t := by
  change WP isa (.block ([loadKey j] ++ [loadKey (j + 1)])) s _
  rw [WP.block_append_iff]
  refine WP.mono (loadNext_ok j s hk (by omega) (by omega) hL) fun t ⟨hL', hk', hf⟩ => ?_
  exact WP.mono (loadNext_ok (j + 1) t hk' (by omega) (by omega) hL')
    fun u ⟨hL'', hk'', hf'⟩ => ⟨hL'', hk'', hf.trans hf'⟩

theorem loadLast_ok {nr : Nat} {w : List Byte} (s : State) (hk : MemKeys nr w s)
    (hL : Loaded nr s) (hr10 : s.gpr .r10 = s.gpr .rdi + BitVec.ofNat 64 (16 * nr)) :
    WP isa (.block [.vbroadcasti32x4H .xmm31 (at_ .r10 0)]) s fun t =>
      Keys nr w t ∧ ZFrame [] s t := by
  let a := s.gpr .rdi + BitVec.ofNat 64 (16 * nr)
  let v := s.mem.readW a 128
  have ea : s.ea (at_ .r10 0) = a := by simp [ea_at, hr10, a]
  have hin : InRegions (s.rd ++ s.wr) (s.ea (at_ .r10 0)) 16 := by
    rw [ea]; exact hk.keys nr (Nat.le_refl _)
  rw [WP.block_cons_iff]
  refine ⟨s.setZH .xmm31 v v v v,
    by rw [ea] at hin
       simp only [isa, exec, State.load128, ea, hin, ite_true, Option.map_some]; rfl, WP.block_nil ?_⟩
  have hf := s.setZH_zframe .xmm31 v v v v
  refine ⟨⟨VaesZ.ZFrame.of_keys hk hf, fun j hj h14 l hl => ?_, fun l hl => ?_⟩, hf⟩
  · rw [State.zlaneH_setZH _ _ _ _ _ _ _ hl]
    simp only [keyReg_ne_last j h14, ite_false]
    exact hL j hj l hl
  · rw [State.zlaneH_setZH _ _ _ _ _ _ _ hl]
    simp only [ite_true, pick4]
    split <;> (try split) <;> (try split) <;> rfl

/-- The preload establishes all inner keys and the final key, preserving
the memory, pointers and low vector registers used by the GCM setup. -/
theorem loadKeys_ok {nr : Nat} {w : List Byte} (s : State) (hk : MemKeys nr w s)
    (hnr : nr = 10 ∨ nr = 12 ∨ nr = 14) (hrsi : s.gpr .rsi = BitVec.ofNat 64 nr)
    (hr10 : s.gpr .r10 = s.gpr .rdi + BitVec.ofNat 64 (16 * nr)) :
    WP isa loadKeys s fun t => Keys nr w t ∧ ZFrame [] s t := by
  have hnr10 : 10 ≤ nr := by rcases hnr with h | h | h <;> omega
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (loadPrefix_ok 10 s hk hnr10 (by decide)) fun t ⟨hL, hk', hf⟩ => ?_
  refine WP.mono (cmpRsiZ_ok t 10 nr (by rw [hf.gpr, hrsi])) fun u ⟨hz, fc⟩ => ?_
  have hu := Loaded.keep hL fc
  have ku := VaesZ.ZFrame.of_keys hk' fc.toZFrame
  have fu := hf.trans fc.toZFrame
  refine WP.seq ?_
  have rest : WP isa
      (.ite .e (.block [])
        (.seq (.block [loadKey 10, loadKey 11, .alu .cmp .rsi (.imm 12)])
          (.ite .e (.block []) (.block [loadKey 12, loadKey 13])))) u
      (fun v => Loaded nr v ∧ MemKeys nr w v ∧ ZFrame [] s v) := by
    rcases hnr with rfl | rfl | rfl
    · exact WP.ite true (by simp [eval, hz]) (fun _ => WP.block_nil ⟨hu, ku, fu⟩)
        (fun h => absurd h (by decide))
    all_goals
      refine WP.ite false (by simp [eval, hz]) (fun h => absurd h (by decide)) fun _ => ?_
      refine WP.seq ?_
      change WP isa (.block ([loadKey 10, loadKey 11] ++ [.alu .cmp .rsi (.imm 12)])) u _
      rw [WP.block_append_iff]
      refine WP.mono (loadTwo_ok 10 u ku (by decide) (by decide) hu) fun v ⟨hv, kv, fv⟩ => ?_
      have hvsi := (congrArg (fun f => f Reg.rsi) (fv.gpr.trans fu.gpr)).trans hrsi
      refine WP.mono (cmpRsiZ_ok v 12 _ hvsi) fun z ⟨hz', fz⟩ => ?_
      have hlz := Loaded.keep hv fz
      have kz := VaesZ.ZFrame.of_keys kv fz.toZFrame
      have fsz := fu.trans (fv.trans fz.toZFrame)
    · exact WP.ite true (by simp [eval, hz']) (fun _ => WP.block_nil ⟨hlz, kz, fsz⟩)
        (fun h => absurd h (by decide))
    · refine WP.ite false (by simp [eval, hz']) (fun h => absurd h (by decide)) fun _ => ?_
      exact WP.mono (loadTwo_ok 12 z kz (by decide) (by decide) hlz)
        fun v ⟨hv, kv, fv⟩ => ⟨hv, kv, fsz.trans fv⟩
  refine WP.mono rest fun v ⟨hv, kv, fv⟩ => ?_
  exact WP.mono (loadLast_ok v kv hv (by rw [fv.gpr, hr10]))
    fun t ⟨kt, ft⟩ => ⟨kt, fv.trans ft⟩

end VG.Proof.Aes.X86_64.VaesZH
