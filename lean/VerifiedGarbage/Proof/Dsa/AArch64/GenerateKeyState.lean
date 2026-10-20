module

public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignRunning
public import VerifiedGarbage.Proof.Dsa.AArch64.GenerateKeyABI
public import VerifiedGarbage.Proof.Dsa.AArch64.GenerateKeyEntry
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.AArch64.GenerateKeyCheck
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCallMemory
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block

/-! # Key generation's frame state, through its entry and the domain check -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

/-- A callee keeps every byte of the wrapper's frame. -/
theorem keygen_call_frameBytes {extra : Nat} {s : State} {wr : List Region} {m m' : Mem}
    (h : GenerateKeyABI extra s)
    (hwr : ∀ r ∈ wr, r.Disjoint ⟨randomBase s, Random.frameBytes⟩)
    (hf : Frame (wr ++ [below (randomBase s) extra]) m m') :
    ∀ i < Random.frameBytes, m' (off (randomBase s) i) = m (off (randomBase s) i) := by
  have hl := h.stackLower
  have hb := (s.sp).isLt
  intro i hi
  apply hf.bytes (R := ⟨randomBase s, Random.frameBytes⟩) _ (by change 256 ≤ 2 ^ 64; decide) hi
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact (hwr r hr).symm
  · simp only [List.mem_singleton] at hr
    subst hr
    exact Offset.base_disjoint_below _ (by unfold Random.frameBytes; omega)

/-- A callee keeps a buffer apart from what it writes and from the stack. -/
theorem keygen_call_inputBytes {extra : Nat} {s : State} {wr : List Region} {m m' : Mem} {p : Addr} {n : Nat}
    (hf : Frame (wr ++ [below (randomBase s) extra]) m m')
    (hwr : ∀ r ∈ wr, r.Disjoint ⟨p, n⟩)
    (hstack : (below (s.sp) (extra + 256)).Disjoint ⟨p, n⟩) (hn : n ≤ 2 ^ 64) :
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
    (hf : Frame (wr ++ [below (randomBase s) extra]) t.mem u.mem)
    (hrd : u.rd = t.rd) (hwr : u.wr = t.wr)
    (hwrs : ∀ r ∈ wr, r.Disjoint ⟨p, bs.length⟩)
    (hstack : (below (s.sp) (extra + 256)).Disjoint ⟨p, bs.length⟩)
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
  sp : t.sp = randomBase s
  saved : KeygenSaved s t.mem
  usedWord : word t.mem (randomBase s) Random.oUsed = BitVec.ofNat 64 used
  rd : t.rd = s.rd
  wr : t.wr = ⟨randomBase s, Random.frameBytes⟩ :: s.wr
  params : Src t (randomBase s) Random.frameBytes (s.gpr .x3) (keygenInput s).params
  rand : Src t (randomBase s) Random.frameBytes (s.gpr .x7) (keygenInput s).rand
  callee : ∀ r ∈ preserved, t.gpr r = s.gpr r
  vectors : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64
  link : word t.mem (randomBase s) RandomSign.oLink = s.gpr .x30

/-- After a change of the frame's private words and scratch registers only. -/
theorem KeygenState.of_frame {extra : Nat} {s t u : State} {h : GenerateKeyABI extra s} {used : Nat}
    (ht : KeygenState h used t) (hf : InScr (randomBase s) Random.frameBytes t.mem u.mem)
    (hw : ∀ d, 40 ≤ d → d + 8 ≤ 152 → word u.mem (randomBase s) d = word t.mem (randomBase s) d)
    (hk : Keep randomVolatile t u)
    (hlink : word u.mem (randomBase s) RandomSign.oLink = word t.mem (randomBase s) RandomSign.oLink) :
    KeygenState h used u :=
  ⟨ht.scr.congr hk.wr, hk.sp.trans ht.sp,
    ht.saved.congr (fun d hd hd' => hw d hd (by omega)), (hw _ (by decide) (by decide)).trans ht.usedWord,
    hk.rd.trans ht.rd, hk.wr.trans ht.wr, ht.params.congrK hf hk, ht.rand.congrK hf hk,
    fun r hc => (hk.gpr r (random_saved_not_volatile hc)).trans (ht.callee r hc),
    fun r hc => (hk.vcs r hc).trans (ht.vectors r hc), hlink.trans ht.link⟩

theorem keygen_head {extra : Nat} {s : State} (h : GenerateKeyABI extra s) :
    WP isa (.block (GenerateKey.entry ++ GenerateKey.checkArgs)) (allocated Random.frameBytes s) fun t =>
      KeygenState h 0 t ∧ word t.mem (randomBase s) Random.oStatus = 0 ∧
      word t.mem (randomBase s) Random.oQ = s.gpr .x3 + s.gpr .x5 ∧ t.gpr .x0 = s.gpr .x3 ∧ t.gpr .x1 = s.gpr .x4 ∧ t.gpr .x2 = s.gpr .x5 ∧
      t.gpr .x3 = s.gpr .x6 ∧ t.gpr .x4 = stackArg s 1 ∧ t.gpr .x5 = stackArg s 2 := by
  have hsp : (allocated Random.frameBytes s).sp = randomBase s := rfl
  rw [WP.block_append_iff]
  refine WP.mono (keygen_entry_ok (keygen_alloc_scr h) hsp (keygen_incoming_read h))
    fun u ⟨hum, hku⟩ => ?_
  have hus := (keygen_alloc_scr h).congr hku.wr
  have husp := hku.sp.trans hsp
  have hsaved : KeygenSaved s u.mem := by rw [hum]; exact keygen_saved_entry s
  have hframe : InScr (randomBase s) Random.frameBytes (allocated Random.frameBytes s).mem u.mem := by
    rw [hum]
    exact InScr.of_outside (keygen_entry_outside _ _) (by decide)
  have hv (p : Nat × BitVec 64) (hp : p ∈ keygenEntryValues (allocated Random.frameBytes s) (randomBase s)) :
      word u.mem (randomBase s) p.1 = p.2 := by
    rw [hum]; exact keygen_entry_values _ _ p hp
  refine WP.mono (keygen_checkArgs_ok hus husp hsaved)
    fun t ⟨h1, h2, h3, h4, h5, h6, htm, hkt⟩ => ?_
  have hk := hku.trans hkt
  have hkv : Keep randomVolatile (allocated Random.frameBytes s) t := hk.mono (by decide)
  refine ⟨⟨hus.congr hkt.wr, hkt.sp.trans husp, by rw [htm]; exact hsaved,
    by rw [htm]; exact hv (144, 0) (by simp [keygenEntryValues]), hk.rd, hk.wr,
    ((keygen_initial_params h).congrK hframe hku).congrK (by rw [htm]; exact InScr.refl _ _ _) hkt,
    ((keygen_initial_rand h).congrK hframe hku).congrK (by rw [htm]; exact InScr.refl _ _ _) hkt,
    fun r hr => hkv.gpr r (random_saved_not_volatile hr),
    hk.vcs,
    by rw [htm]; exact hv (232, s.gpr .x30) (by simp [keygenEntryValues, allocated])⟩,
    by rw [htm]; exact hv (192, 0) (by simp [keygenEntryValues]),
    by rw [htm]; exact hv (168, _) (by simp [keygenEntryValues, allocated]), h1, h2, h3, h4, h5, h6⟩

end VG.Proof.Dsa.AArch64
