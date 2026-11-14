module
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignEnv
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignInputs
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignSaved
import VerifiedGarbage.Proof.Dsa.X86_64.RandomPrepareState
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

/-! ### `Dsa.X86_64.RandomSignInit`, which only this module used -/

section

/-! Initialize randomized signing from the shared ABI's arguments. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

theorem random_sign_init {extra : Nat} {s : State} (h : RandomSignABI extra s)
    (hq : 1 < Spec.Dsa.decodeBE (randomQBytes s)) :
    WP isa (.seq (.block RandomSign.entry) Random.prepare) (allocState Random.frameBytes s) fun t =>
      ((∃ m draws, t.gpr .rax = 1 ∧ RandomReady (randomContextOf h m hq) 0 draws t) ∧
      RandomSaved s t.mem ∧ word t.mem (randomBase s) Random.oAttempts = 8 ∧
      Src t (randomBase s) Random.frameBytes (s.gpr .rcx) (randomInput s).key ∧
      Src t (randomBase s) Random.frameBytes (stackArg s 1) (randomInput s).digest) ∧
      Keep [.rax, .rcx, .rsi, .r8, .r9, .r10, .r11] (allocState Random.frameBytes s) t := by
  refine WP.keep [.rax, .rcx, .rsi, .r8, .r9, .r10, .r11] ?_ (by rfl)
  have hsp : (allocState Random.frameBytes s).gpr .rsp = randomBase s := by
    simp only [allocState, State.setReg, ite_true]; rfl
  refine WP.seq (WP.mono (random_entry_ok (random_alloc_scr h) hsp (random_incoming_read h))
    fun u ⟨hum, hku⟩ => ?_)
  have hus := (random_alloc_scr h).congr hku.2.2
  have husp := (hku.gpr (by decide)).trans hsp
  have hsaved : RandomSaved s u.mem := by rw [hum]; exact random_saved_entry s
  have hframe : InScr (randomBase s) Random.frameBytes (allocState Random.frameBytes s).mem u.mem := by
    rw [hum]
    exact InScr.of_outside (random_entry_outside _ _) (by decide)
  have hqs := (random_initial_q h).congrK hframe hku
  have hrs := (random_initial_rand h).congrK hframe hku
  have hv (p : Nat × BitVec 64) (hp : p ∈ randomEntryValues (allocState Random.frameBytes s) (randomBase s)) :
      word u.mem (randomBase s) p.1 = p.2 := by
    rw [hum]; exact random_entry_values _ _ p hp
  have hqu : word u.mem (randomBase s) Random.oQ = s.gpr .rcx + s.gpr .r9 :=
    hv (168, s.gpr .rcx + s.gpr .r9) (by simp [randomEntryValues, allocState, State.setReg])
  have huu : word u.mem (randomBase s) Random.oUsed = 0 :=
    hv (144, 0) (by simp [randomEntryValues])
  have hau : word u.mem (randomBase s) Random.oAttempts = 8 :=
    hv (152, 8) (by simp [randomEntryValues])
  let C := randomContextOf h u.mem hq
  have hr : word u.mem C.B Random.oRand = C.R :=
    hsaved (112, stackArg s 3) (by simp [randomSavedValues])
  have hrl : word u.mem C.B Random.oRandLen = BitVec.ofNat 64 C.rand.length := by
    simpa only [Random.oRandLen, C, randomContextOf, randomInput, bytesAt_length, ofNat_toNat64] using
      hsaved (120, stackArg s 4) (by simp [randomSavedValues])
  have hql : word u.mem C.B Random.oQLen = BitVec.ofNat 64 C.qBytes.length := by
    simpa only [Random.oQLen, C, randomContextOf, random_q_length h, ofNat_toNat64] using
      hsaved (88, stackArg s 0) (by simp [randomSavedValues])
  refine WP.mono (WP.keep [.rax, .rcx, .rsi, .r8, .r9, .r10, .r11] (random_prepare_ready (C := C) (draws := (word u.mem C.B Random.oDraws).toNat)
    hus husp hr hrl huu (ofNat_toNat64 _).symm hqu hql hrs hqs (Frm.refl _ _ _) (Nat.zero_le _) hq) rfl)
    fun t ⟨⟨hta, htr⟩, hkp⟩ => ?_
  have hw (d : Nat) (hd : d + 8 ≤ 144 ∨ d = 152) : word t.mem (randomBase s) d = word u.mem (randomBase s) d := by
    apply htr.frame.word_eq
    · intro r hr
      simp only [randomWriteRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> dsimp only <;> omega_using [hd]
    · omega_using [hd]
  have hpf : InScr (randomBase s) Random.frameBytes u.mem t.mem := InScr.of_frm htr.frame (by
    intro r hr
    simp only [randomWriteRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> decide)
  exact ⟨⟨u.mem, _, hta, htr⟩, hsaved.congr (fun d _ hd => hw d (Or.inl hd)),
    (hw _ (Or.inr rfl)).trans hau,
    ((random_initial_key h).congrK hframe hku).congrK hpf hkp,
    ((random_initial_digest h).congrK hframe hku).congrK hpf hkp⟩

end VG.Proof.Dsa.X86_64

end

end


/-! The persistent state of the bounded randomized-signing loop. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

def randomVolatile : List Reg := [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11]

theorem random_saved_not_volatile {r : Reg} (h : r ∈ calleeSaved) : r ∉ randomVolatile := by
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

structure RandomSignRunning {extra : Nat} {s : State} (h : RandomSignABI extra s)
    (hq : 1 < Spec.Dsa.decodeBE (randomQBytes s)) (used fuel : Nat) (t : State) : Prop where
  ready : ∃ m draws, RandomReady (randomContextOf h m hq) used draws t
  saved : RandomSaved s t.mem
  attempts : word t.mem (randomBase s) Random.oAttempts = BitVec.ofNat 64 fuel
  rd : t.rd = s.rd
  wr : t.wr = ⟨randomBase s, Random.frameBytes⟩ :: s.wr
  key : Src t (randomBase s) Random.frameBytes (s.gpr .rcx) (randomInput s).key
  digest : Src t (randomBase s) Random.frameBytes (stackArg s 1) (randomInput s).digest
  callee : ∀ r ∈ calleeSaved, r ≠ .rsp → t.gpr r = s.gpr r
  mxcsr : t.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10

theorem random_sign_init_running {extra : Nat} {s : State} (h : RandomSignABI extra s)
    (hq : 1 < Spec.Dsa.decodeBE (randomQBytes s)) :
    WP isa (.seq (.block RandomSign.entry) Random.prepare) (allocState Random.frameBytes s) fun t =>
      t.gpr .rax = 1 ∧ RandomSignRunning h hq 0 8 t := by
  refine WP.mono_mx (by decide) (random_sign_init h hq)
    fun t ⟨⟨⟨m, draws, hrax, hr⟩, hs, ha, hkey, hdigest⟩, hk⟩ hmx => ?_
  have hkv : Keep randomVolatile (allocState Random.frameBytes s) t := hk.mono (by decide)
  refine ⟨hrax, ⟨m, draws, hr⟩, hs, ha, hk.2.1, hk.2.2, hkey, hdigest, ?_, ?_⟩
  · intro r hr hne
    rw [hkv.gpr (random_saved_not_volatile hr)]
    simp only [allocState, State.setReg, ite_eq_right hne]
  · rw [hmx]
    rfl

theorem RandomSignRunning.congr {extra : Nat} {s t u : State} {h : RandomSignABI extra s}
    {hq : 1 < Spec.Dsa.decodeBE (randomQBytes s)} {used fuel : Nat}
    (hr : RandomSignRunning h hq used fuel t) (hm : u.mem = t.mem) (hk : Keep [.rax] t u)
    (hmx : u.mxcsr = t.mxcsr) : RandomSignRunning h hq used fuel u := by
  obtain ⟨m, draws, hready⟩ := hr.ready
  have hf : InScr (randomBase s) Random.frameBytes t.mem u.mem := by rw [hm]; exact InScr.refl _ _ _
  refine ⟨⟨m, draws, hready.congr hm hk⟩, by rw [hm]; exact hr.saved,
    by rw [hm]; exact hr.attempts, hk.2.1.trans hr.rd, hk.2.2.trans hr.wr,
    hr.key.congrK hf hk, hr.digest.congrK hf hk, ?_, ?_⟩
  · intro r hc hne
    exact ((hk.mono (show ∀ r ∈ [Reg.rax], r ∈ randomVolatile by decide)).gpr
      (random_saved_not_volatile hc)).trans (hr.callee r hc hne)
  · rw [hmx]; exact hr.mxcsr

end VG.Proof.Dsa.X86_64
