module

public import VerifiedGarbage.Proof.Dsa.X86_64.GenerateKeyCheck
import VerifiedGarbage.Proof.Bignum.X86_64.FoldedExp
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCallMemory
import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignRunning
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-! ### `Dsa.X86_64.GenerateKeyState`, which this module and modules that import it used -/

section

/-! # Key generation's frame state, through its entry and the domain check -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

/-- A callee keeps every byte of the wrapper's frame. -/
theorem keygen_call_frameBytes {extra : Nat} {s : State} {wr : List Region} {m m' : Mem}
    (h : GenerateKeyABI extra s)
    (hwr : ∀ r ∈ wr, r.Disjoint ⟨randomBase s, Random.frameBytes⟩)
    (hf : Frame (wr ++ [below (randomBase s) (extra + 8)]) m m') :
    ∀ i < Random.frameBytes, m' (off (randomBase s) i) = m (off (randomBase s) i) := by
  have hl := h.stackLower
  have hb := (s.gpr .rsp).isLt
  intro i hi
  apply hf.bytes (R := ⟨randomBase s, Random.frameBytes⟩) _ (by change 248 ≤ 2 ^ 64; decide) hi
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact (hwr r hr).symm
  · simp only [List.mem_singleton] at hr
    subst hr
    exact Offset.base_disjoint_below _ (by unfold Random.frameBytes; omega_using [hl])

/-- A callee keeps a buffer apart from what it writes and from the stack. -/
theorem keygen_call_inputBytes {extra : Nat} {s : State} {wr : List Region} {m m' : Mem} {p : Addr} {n : Nat}
    (hf : Frame (wr ++ [below (randomBase s) (extra + 8)]) m m')
    (hwr : ∀ r ∈ wr, r.Disjoint ⟨p, n⟩)
    (hstack : (below (s.gpr .rsp) (extra + 256)).Disjoint ⟨p, n⟩) (hn : n ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m' p n = Spec.Rsa.bytesAt m p n := by
  unfold Spec.Rsa.bytesAt
  apply List.map_congr_left
  intro i hi
  apply hf.bytes (R := ⟨p, n⟩) _ hn (List.mem_range.mp hi)
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact (hwr r hr).symm
  · simp only [List.mem_singleton] at hr
    subst hr
    exact (hstack.sub_left (random_calleeFrame_sub extra s)).symm

theorem keygen_call_source {extra : Nat} {s t u : State} {wr : List Region} {p : Addr} {bs : List Byte}
    (hsrc : Src t (randomBase s) Random.frameBytes p bs)
    (hf : Frame (wr ++ [below (randomBase s) (extra + 8)]) t.mem u.mem)
    (hrd : u.rd = t.rd) (hwr : u.wr = t.wr)
    (hwrs : ∀ r ∈ wr, r.Disjoint ⟨p, bs.length⟩)
    (hstack : (below (s.gpr .rsp) (extra + 256)).Disjoint ⟨p, bs.length⟩)
    (hn : bs.length ≤ 2 ^ 64) : Src u (randomBase s) Random.frameBytes p bs := by
  refine ⟨fun i hi => by rw [hrd, hwr]; exact hsrc.rd i hi, ?_, hsrc.out⟩
  intro i hi
  have hbytes := keygen_call_inputBytes hf hwrs hstack hn
  have he := congrArg (fun xs : List Byte => xs[i]?) hbytes
  simp only [Spec.Rsa.bytesAt, List.getElem?_map, List.getElem?_range,
    hi, Option.map_some] at he
  exact (Option.some.inj he).trans (hsrc.val i hi)

/-- The wrapper's frame between its steps, `used` draws in. -/
structure KeygenState {extra : Nat} {s : State} (h : GenerateKeyABI extra s) (used : Nat) (t : State) : Prop where
  scr : Scr t (randomBase s) Random.frameBytes
  sp : t.gpr .rsp = randomBase s
  saved : KeygenSaved s t.mem
  usedWord : word t.mem (randomBase s) Random.oUsed = BitVec.ofNat 64 used
  rd : t.rd = s.rd
  wr : t.wr = ⟨randomBase s, Random.frameBytes⟩ :: s.wr
  params : Src t (randomBase s) Random.frameBytes (s.gpr .rcx) (keygenInput s).params
  rand : Src t (randomBase s) Random.frameBytes (stackArg s 1) (keygenInput s).rand
  callee : ∀ r ∈ calleeSaved, r ≠ .rsp → t.gpr r = s.gpr r
  mxcsr : t.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10

/-- After a change of the frame's private words and scratch registers only. -/
theorem KeygenState.of_frame {extra : Nat} {s t u : State} {h : GenerateKeyABI extra s} {used : Nat}
    (ht : KeygenState h used t) (hf : InScr (randomBase s) Random.frameBytes t.mem u.mem)
    (hw : ∀ d, 40 ≤ d → d + 8 ≤ 152 → word u.mem (randomBase s) d = word t.mem (randomBase s) d)
    (hk : Keep randomVolatile t u) (hmx : u.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10) :
    KeygenState h used u :=
  ⟨ht.scr.congr hk.2.2, (hk.gpr (by decide)).trans ht.sp,
    ht.saved.congr (fun d hd hd' => hw d hd (by omega_using [hd'])), (hw _ (by decide) (by decide)).trans ht.usedWord,
    hk.2.1.trans ht.rd, hk.2.2.trans ht.wr, ht.params.congrK hf hk, ht.rand.congrK hf hk,
    fun r hc hn => (hk.gpr (random_saved_not_volatile hc)).trans (ht.callee r hc hn), hmx.trans ht.mxcsr⟩

theorem keygen_head {extra : Nat} {s : State} (h : GenerateKeyABI extra s) :
    WP isa (.block (GenerateKey.entry ++ GenerateKey.checkArgs)) (allocState Random.frameBytes s) fun t =>
      KeygenState h 0 t ∧ word t.mem (randomBase s) Random.oStatus = 0 ∧
      word t.mem (randomBase s) Random.oQ = s.gpr .rcx + s.gpr .r9 ∧ t.gpr .rdi = s.gpr .rcx ∧ t.gpr .rsi = s.gpr .r8 ∧ t.gpr .rdx = s.gpr .r9 ∧
      t.gpr .rcx = stackArg s 0 ∧ t.gpr .r8 = stackArg s 3 ∧ t.gpr .r9 = stackArg s 4 := by
  have hsp : (allocState Random.frameBytes s).gpr .rsp = randomBase s := by
    simp only [allocState, State.setReg, ite_true]; rfl
  rw [WP.block_append_iff]
  refine WP.mono_mx (by decide) (keygen_entry_ok (keygen_alloc_scr h) hsp (keygen_incoming_read h))
    fun u ⟨hum, hku⟩ hmxu => ?_
  have hus := (keygen_alloc_scr h).congr hku.2.2
  have husp := (hku.gpr (by decide)).trans hsp
  have hsaved : KeygenSaved s u.mem := by rw [hum]; exact keygen_saved_entry s
  have hframe : InScr (randomBase s) Random.frameBytes (allocState Random.frameBytes s).mem u.mem := by
    rw [hum]
    exact InScr.of_outside (keygen_entry_outside _ _) (by decide)
  have hv (p : Nat × BitVec 64) (hp : p ∈ keygenEntryValues (allocState Random.frameBytes s) (randomBase s)) :
      word u.mem (randomBase s) p.1 = p.2 := by
    rw [hum]; exact keygen_entry_values _ _ p hp
  refine WP.mono_mx (by decide) (keygen_checkArgs_ok hus husp hsaved)
    fun t ⟨h1, h2, h3, h4, h5, h6, htm, hkt⟩ hmxt => ?_
  have hk := hku.trans hkt
  have hkv : Keep randomVolatile (allocState Random.frameBytes s) t := hk.mono (by decide)
  refine ⟨⟨hus.congr hkt.2.2, (hkt.gpr (by decide)).trans husp, by rw [htm]; exact hsaved,
    by rw [htm]; exact hv (144, 0) (by simp [keygenEntryValues]), hk.2.1, hk.2.2,
    ((keygen_initial_params h).congrK hframe hku).congrK (by rw [htm]; exact InScr.refl _ _ _) hkt,
    ((keygen_initial_rand h).congrK hframe hku).congrK (by rw [htm]; exact InScr.refl _ _ _) hkt,
    fun r hr hne => by
      rw [hkv.gpr (random_saved_not_volatile hr)]
      simp only [allocState, State.setReg, ite_eq_right hne],
    by rw [hmxt, hmxu]; rfl⟩,
    by rw [htm]; exact hv (192, 0) (by simp [keygenEntryValues]),
    by rw [htm]; exact hv (168, _) (by simp [keygenEntryValues, allocState, State.setReg]), h1, h2, h3, h4, h5, h6⟩

end VG.Proof.Dsa.X86_64

end

end

/-! # Key generation's domain check, on its frame state -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

/-- Whether the domain is one key generation accepts. -/
abbrev keygenChecked (s : State) : Bool :=
  Spec.Dsa.checkParametersBytes (keygenInput s).pLen (keygenInput s).qLen (keygenInput s).params

/-- After a call: the frame's bytes kept, the inputs kept, the callee-saved
registers kept. -/
theorem KeygenState.after_call {extra : Nat} {s t u : State} {h : GenerateKeyABI extra s} {used : Nat}
    {wr : List Region} (ht : KeygenState h used t)
    (hwrF : ∀ r ∈ wr, r.Disjoint ⟨randomBase s, Random.frameBytes⟩)
    (hwrP : ∀ r ∈ wr, r.Disjoint ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩)
    (hwrR : ∀ r ∈ wr, r.Disjoint ⟨stackArg s 1, (stackArg s 2).toNat⟩)
    (hf : Frame (wr ++ [below (randomBase s) (extra + 8)]) t.mem u.mem)
    (hur : u.rd = t.rd) (huw : u.wr = t.wr) (huc : ∀ r ∈ calleeSaved, u.gpr r = t.gpr r)
    (hmx : u.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10) :
    KeygenState h used u ∧
      ∀ d, d + 8 ≤ Random.frameBytes → word u.mem (randomBase s) d = word t.mem (randomBase s) d := by
  have hb := keygen_call_frameBytes h hwrF hf
  have hw (d : Nat) (hd : d + 8 ≤ Random.frameBytes) := random_frame_words hb hd
  have hpl : (keygenInput s).params.length = (s.gpr .r8).toNat := bytesAt_length _ _ _
  have hrl : (keygenInput s).rand.length = (stackArg s 2).toNat := bytesAt_length _ _ _
  refine ⟨⟨ht.scr.congr huw, (huc .rsp (by decide)).trans ht.sp,
    ht.saved.congr (fun d _ hd => hw d (by unfold Random.frameBytes; omega_using [hd])),
    (hw _ (by decide)).trans ht.usedWord, hur.trans ht.rd, huw.trans ht.wr,
    keygen_call_source ht.params hf hur huw (by rw [hpl]; exact hwrP) (by rw [hpl]; exact h.stackParams)
      (by rw [hpl]; exact Nat.le_of_lt (s.gpr .r8).isLt),
    keygen_call_source ht.rand hf hur huw (by rw [hrl]; exact hwrR) (by rw [hrl]; exact h.stackRand)
      (by rw [hrl]; exact Nat.le_of_lt (stackArg s 2).isLt),
    fun r hc hn => (huc r hc).trans (ht.callee r hc hn), hmx.trans ht.mxcsr⟩, hw⟩

theorem keygen_check_step (v : Backend) {s t : State} {h : GenerateKeyABI v.stack s}
    (ht : KeygenState h 0 t)
    (hdi : t.gpr .rdi = s.gpr .rcx) (hsi : t.gpr .rsi = s.gpr .r8) (hdx : t.gpr .rdx = s.gpr .r9)
    (hcx : t.gpr .rcx = stackArg s 0) (h8 : t.gpr .r8 = stackArg s 3) (h9 : t.gpr .r9 = stackArg s 4) :
    WP isa (.call (keygenCheckName v) (Generate.checkParameters v.sq v.mul)) t fun u =>
      KeygenState h 0 u ∧
      (∀ d, d + 8 ≤ Random.frameBytes → word u.mem (randomBase s) d = word t.mem (randomBase s) d) ∧
      ((u.gpr .rax).setWidth 32).toNat = if keygenChecked s then 1 else 0 := by
  refine WP.mono (keygen_check_call v h ht.sp hdi hsi hdx hcx h8 h9 ht.rd ht.wr)
    fun u ⟨hur, huw, huc, hf, hres, hmx⟩ => ?_
  have hscratch : (⟨stackArg s 3, (stackArg s 4).toNat * 8⟩ : Region).Disjoint ⟨randomBase s, Random.frameBytes⟩ :=
    (h.stackScratch.sub_left (keygen_frame_sub h)).symm
  obtain ⟨hu, hw⟩ := ht.after_call (wr := keygenCheckWr s)
    (fun r hr => by simp only [keygenCheckWr, List.mem_singleton] at hr; subst hr; exact hscratch)
    (fun r hr => by simp only [keygenCheckWr, List.mem_singleton] at hr; subst hr; exact h.paramsScratch.symm)
    (fun r hr => by simp only [keygenCheckWr, List.mem_singleton] at hr; subst hr; exact h.randScratch.symm)
    hf hur huw huc hmx
  refine ⟨hu, hw, ?_⟩
  rw [hres]
  have hp : Spec.Rsa.bytesAt t.mem (s.gpr .rcx) (s.gpr .r8).toNat = (keygenInput s).params := by
    simpa only [keygenInput, bytesAt_length] using FoldedPublic.src_bytesAt ht.params
  rw [hp]

end VG.Proof.Dsa.X86_64
