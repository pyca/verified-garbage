module

-- separate module: the calls on either lanes, which `forsPk`'s proofs use too

public import VerifiedGarbage.Proof.SlhDsa.X86_64.VerifyPkPathLoop
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsCorrect

/-!
# SLH-DSA on x86-64, `xmssPk`: calls of `thash4` and the WOTS⁺ public key

`lanes_ok`: a call of `thash4` on the lanes `A` or `B` (`thashCall`), whose
outputs are `SHAKE256` of the lanes' messages, and which changes only what
`changes` lists and the stack below. `wotsPk_ok`: the block of `wotsPk`
(`Impl/SlhDsa/X86_64/Verify.lean`), which compresses the chains' ends in
lane 0 of `B` into the WOTS⁺ public key, in lane 0 of `A`'s message.
-/

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64

open VG VG.X86_64
open VG.Impl.SlhDsa.X86_64 (Layout)
open VG.Spec.Sha3 (bytesAt shake256)
open VG.Spec.SlhDsa
open VG.Impl.SlhDsa.X86_64 (setField setFieldR)
open VG.Proof.SlhDsa.X86_64.Levels (sx_ofNat add_add toNat_at)

/-- The outputs of a call of `thash4` on the lanes at `o`, `st` bytes apart. -/
def lanesOut (p : Params) (S : Addr) (o st : Nat) : List Region :=
  (List.range 4).map fun j => ⟨at' S (o + st * j + p.n + 32), p.n⟩

/-- A call of `thash4` on the lanes at `o` (those of `A` or `B`), messages of
`len` bytes. -/
theorem lanes_ok {p : Params} (T : Thash4Impl p.n) (name : String) (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32)
    {stack : Nat} (hst : T.stack + 16 ≤ stack) (hs63 : stack < 2 ^ 63) {o st len : Nat}
    (hl : (o = Layout.oA ∧ st = Layout.strideA) ∨ (o = Layout.oB ∧ st = Layout.strideB))
    (hlp : 0 < len) (hlm : len % 8 = 0) (hll : len ≤ st)
    {S : Addr} {t : State} (hbx : t.gpr .rbx = S) (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ t.wr)
    (hS : S.toNat + 2 ^ 16 ≤ 2 ^ 64) (hstk : (below (t.gpr .rsp) stack).Disjoint ⟨S, 2 ^ 16⟩)
    (hrc : RcTable t.mem S) {Q : State → Prop}
    (k : ∀ t', t'.rd = t.rd → t'.wr = t.wr → (∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) →
      (∀ j < 4, bytesAt t'.mem (at' S (o + st * j + p.n + 32)) p.n =
        shake256 (bytesAt t.mem (at' S (o + st * j)) len) p.n) →
      Frame (changes p S ++ [below (t.gpr .rsp) stack]) t.mem t'.mem →
      Frame (lanesOut p S o st ++ [⟨S, 1600⟩, ⟨at' S 2368, 32⟩, below (t.gpr .rsp) stack]) t.mem t'.mem → Q t') :
    WP isa (Impl.SlhDsa.X86_64.thashCall ⟨p.n, p.len⟩ name T.code o st len) t Q := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have hoS : o + 4 * st ≤ 12640 ∧ o < 2 ^ 31 ∧ st < 2 ^ 31 ∧ 3296 ≤ o ∧ 2 * p.n + 32 ≤ st := by
    rcases hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp only [Layout.oA, Layout.oB, Layout.strideA, Layout.strideB] <;>
      omega_using [hn32]
  obtain ⟨hoS, ho, hst', ho3, hout⟩ := hoS
  unfold Impl.SlhDsa.X86_64.thashCall
  refine WP.seq ?_
  simp only [Impl.SlhDsa.X86_64.thashArgs, Impl.SlhDsa.X86_64.Layout.msgOff]
  refine Proof.Sha3.X86_64.wp_mov fun u₁ v₁ => Proof.Sha3.X86_64.wp_addi fun u₂ v₂ =>
    Proof.Sha3.X86_64.wp_mov32i fun u₃ v₃ => Proof.Sha3.X86_64.wp_mov32i fun u₄ v₄ =>
    Proof.Sha3.X86_64.wp_mov fun u₅ v₅ => Proof.Sha3.X86_64.wp_addi fun u₆ v₆ =>
    Proof.Sha3.X86_64.wp_mov fun u v => WP.block_nil ?_
  have hm : u.mem = t.mem := by rw [v.mem, v₆.mem, v₅.mem, v₄.mem, v₃.mem, v₂.mem, v₁.mem]
  have hrd : u.rd = t.rd := by rw [v.rd, v₆.rd, v₅.rd, v₄.rd, v₃.rd, v₂.rd, v₁.rd]
  have hwr : u.wr = t.wr := by rw [v.wr, v₆.wr, v₅.wr, v₄.wr, v₃.wr, v₂.wr, v₁.wr]
  have hg : ∀ g, g ≠ .rdi → g ≠ .rsi → g ≠ .rdx → g ≠ .rcx → g ≠ .r8 → u.gpr g = t.gpr g := fun g h1 h2 h3 h4 h5 => by
    rw [v.other _ h5, v₆.other _ h4, v₅.other _ h4, v₄.other _ h3, v₃.other _ h2, v₂.other _ h1, v₁.other _ h1]
  have hsp : u.gpr .rsp = t.gpr .rsp := hg _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have hdi2 : u₂.gpr .rdi = at' S o := by rw [v₂.gpr, v₁.gpr, hbx, sx_ofNat ho]
  have hdi : u.gpr .rdi = at' S o := by
    rw [v.other _ (by decide), v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide),
      v₃.other _ (by decide), hdi2]
  have hsi : (u.gpr .rsi).toNat = st := by
    rw [v.other _ (by decide), v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.gpr]
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega_using [hst']
  have hdx : (u.gpr .rdx).toNat = len := by
    rw [v.other _ (by decide), v₆.other _ (by decide), v₅.other _ (by decide), v₄.gpr]
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega_using [hst', hll]
  have hcx : u.gpr .rcx = at' S o + BitVec.ofNat 64 (p.n + 32) := by
    rw [v.other _ (by decide), v₆.gpr, v₅.gpr, v₄.other _ (by decide), v₃.other _ (by decide), hdi2,
      sx_ofNat (by omega_using [hn32])]
  have h8 : u.gpr .r8 = S := by
    rw [v.gpr, v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide),
      v₂.other _ (by decide), v₁.other _ (by decide), hbx]
  have hb8 : Region.Sub (below (u.gpr .rsp) (T.stack + 8)) (below (t.gpr .rsp) stack) := by
    rw [hsp]; exact below_sub (by omega_using [hst]) (by omega_using [hs63])
  have hLs : Region.Sub ⟨at' S o, 4 * st⟩ ⟨S, 2 ^ 16⟩ := Offset.sub_base S (by omega_using [hoS])
  have hWs : Region.Sub ⟨S, workLen⟩ ⟨S, 2 ^ 16⟩ := Region.sub_prefix (by simp [workLen])
  have hw' : (⟨S, 2 ^ 16⟩ : Region) ∈ u.wr := by rw [hwr]; exact hw
  refine thash4_call T name (L := at' S o) (W := S) hdi hsi hdx hcx h8 hlp hlm hll (by omega_using [hout])
    (by rw [toNat_at (by omega_using [hS, hoS])]; omega_using [hS, hoS]) (by simp only [workLen]; omega_using [hS])
    (Offset.disjoint_base S (by simp only [workLen]; omega_using [ho3]) (by omega_using [hoS]))
    ((hstk.sub_left hb8).sub_right hLs) ((hstk.sub_left hb8).sub_right hWs) (by rw [hm]; exact hrc)
    (Covers.of_sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, hw', o, rfl, by show o + 4 * st ≤ 2 ^ 16; omega_using [hoS]⟩
      · exact ⟨_, hw', 0, Levels.scr0 S, by simp [workLen]⟩)
    fun t' h₁ h₂ h₃ h₄ h₅ => ?_
  rw [hm] at h₄ h₅
  refine k t' (by rw [h₁, hrd]) (by rw [h₂, hwr]) (fun r hr => by
      rw [h₃ r hr]
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact hg _ (by decide) (by decide) (by decide) (by decide) (by decide))
    (fun j hj => ?_) (h₅.sub fun r hr => ?_) (h₅.sub fun r hr => ?_)
  · have e₁ : at' S o + BitVec.ofNat 64 (p.n + 32) + BitVec.ofNat 64 (j * st) = at' S (o + st * j + p.n + 32) := by
      rw [at', add_add, add_add, Nat.mul_comm j st]; congr 2; omega_using []
    have e₂ : at' S o + BitVec.ofNat 64 (j * st) = at' S (o + st * j) := by
      rw [at', add_add, Nat.mul_comm j st]
    rw [← e₁, ← e₂]; exact h₄ j hj
  · simp only [t4Changes, List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with ⟨j, hj, rfl⟩ | rfl | rfl | rfl
    · rw [add_add, add_add]
      have hjs : st * j + st ≤ 4 * st := by rw [Nat.mul_comm st j, ← Nat.succ_mul]; exact Nat.mul_le_mul_right st hj
      have hm : ∀ {x : Region} {xs : List Region}, x ∈ xs →
          xs = [⟨at' S (Layout.laneA j + p.n + 16), Layout.strideA - p.n - 16⟩,
            ⟨at' S (Layout.laneB j + p.n + 16), Layout.strideB - p.n - 16⟩] →
          x ∈ changes p S ++ [below (t.gpr .rsp) stack] := fun h e => by
        subst e
        exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
          (List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hj, h⟩)))
      rcases hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · refine ⟨_, hm (List.mem_cons_self ..) rfl, Offset.sub S ?_ ?_⟩ <;>
          simp only [Layout.laneA, Layout.oA, Layout.strideA] at hjs ⊢ <;> omega_using [hn32, hjs]
      · refine ⟨_, hm (List.mem_cons_of_mem _ (List.mem_cons_self ..)) rfl, Offset.sub S ?_ ?_⟩ <;>
          simp only [Layout.laneB, Layout.oB, Layout.strideB] at hjs ⊢ <;> omega_using [hn32, hjs]
    · exact ⟨_, List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_cons_self ..))),
        fun _ h => h⟩
    · exact ⟨_, List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_cons_of_mem _ (List.mem_cons_self ..)))), by simp only [workLen]; exact fun _ h => h⟩
    · exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), hb8⟩
  · simp only [t4Changes, List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with ⟨j, hj, rfl⟩ | rfl | rfl | rfl
    · have e₁ : at' S o + BitVec.ofNat 64 (p.n + 32) + BitVec.ofNat 64 (j * st) = at' S (o + st * j + p.n + 32) := by
        rw [at', add_add, add_add, Nat.mul_comm j st]; congr 2; omega_using []
      rw [e₁]
      exact ⟨_, List.mem_append_left _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩), fun _ h => h⟩
    · exact ⟨_, List.mem_append_right _ (List.mem_cons_self ..), fun _ h => h⟩
    · exact ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)),
        by simp only [workLen]; exact fun _ h => h⟩
    · exact ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))), hb8⟩

/-- The fields of `wotsPk`'s address, in lane 0 of `B`: the type `WOTS_PK`,
the key pair `idx`, and two zero words. -/
theorem wfields_ok {p : Params} (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32)
    {s : State} {S : Addr} {idx : Nat} (hidx : idx < 2 ^ 32)
    (hbx : s.gpr .rbx = S) (h12 : s.gpr .r12 = BitVec.ofNat 64 idx)
    (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ s.wr) {is : List Instr} {Q : State → Prop}
    (k : ∀ s', (∀ g, g ≠ .rax → s'.gpr g = s.gpr g) → s'.rd = s.rd → s'.wr = s.wr →
      bytesAt s'.mem (at' S (Layout.laneB 0 + p.n + 16)) 16 =
        toByte 1 4 ++ toByte idx 4 ++ toByte 0 4 ++ toByte 0 4 →
      Frame [⟨at' S (Layout.laneB 0 + p.n + 16), 16⟩] s.mem s'.mem → WP isa (.block is) s' Q) :
    WP isa (.block ((setField .rbx (Layout.laneB 0 + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 16) 1 ++
        setFieldR .rbx (Layout.laneB 0 + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 20) .r12 ++
        setField .rbx (Layout.laneB 0 + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 24) 0 ++
        setField .rbx (Layout.laneB 0 + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 28) 0) ++ is)) s Q := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have hadr : (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff = p.n := rfl
  rw [hadr]
  have hb0 : Layout.laneB 0 = 3808 := rfl
  obtain ⟨A, hA⟩ : ∃ A, A = Layout.laneB 0 + p.n := ⟨_, rfl⟩
  rw [← hA]
  rw [← hA] at k
  have hAb : A + 32 ≤ 2 ^ 16 := by omega
  have hin : ∀ (t : State) (o : Nat), t.gpr .rbx = S → t.wr = s.wr → o + 4 ≤ 2 ^ 16 →
      InRegions t.wr (t.gpr .rbx + BitVec.ofNat 64 o) 4 := fun t o h₁ h₂ ho => by
    rw [h₁, h₂]; exact Levels.in_scr hw ho
  have hdj : ∀ a c : Nat, a + 4 ≤ c ∨ c + 4 ≤ a → a + 4 ≤ 2 ^ 16 → c + 4 ≤ 2 ^ 16 →
      ∀ r ∈ [(⟨S + BitVec.ofNat 64 c, 4⟩ : Region)], Region.Disjoint ⟨S + BitVec.ofNat 64 a, 4⟩ r :=
    fun a c h h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint S h (by omega) (by omega)
  have hsub : ∀ c : Nat, A + 16 ≤ c → c + 4 ≤ A + 32 →
      ∀ r ∈ [(⟨S + BitVec.ofNat 64 c, 4⟩ : Region)], ∃ r' ∈ [(⟨at' S (A + 16), 16⟩ : Region)], Region.Sub r r' :=
    fun c h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub S h₁ (by omega)⟩
  simp only [List.append_assoc]
  refine setField_ok (by decide) (by decide) (hin s _ hbx rfl (by omega)) fun s₁ f₁ => ?_
  rw [hbx] at f₁
  have hb₁ : s₁.gpr .rbx = S := by rw [f₁.gpr _ (by decide), hbx]
  have hr₁ : s₁.gpr .r12 = BitVec.ofNat 64 idx := by rw [f₁.gpr _ (by decide), h12]
  have hidx' : (BitVec.ofNat 64 idx).toNat = idx := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine setFieldR_ok (by decide) (by rw [hr₁, hidx']; exact hidx) (hin s₁ _ hb₁ f₁.wr (by omega)) fun s₂ f₂ => ?_
  rw [hb₁, hr₁, hidx'] at f₂
  have hb₂ : s₂.gpr .rbx = S := by rw [f₂.gpr _ (by decide), hb₁]
  refine setField_ok (by decide) (by decide) (hin s₂ _ hb₂ (by rw [f₂.wr, f₁.wr]) (by omega)) fun s₃ f₃ => ?_
  rw [hb₂] at f₃
  have hb₃ : s₃.gpr .rbx = S := by rw [f₃.gpr _ (by decide), hb₂]
  refine setField_ok (by decide) (by decide) (hin s₃ _ hb₃ (by rw [f₃.wr, f₂.wr, f₁.wr]) (by omega)) fun s₄ f₄ => ?_
  rw [hb₃] at f₄
  refine k s₄ (fun g h => by rw [f₄.gpr _ h, f₃.gpr _ h, f₂.gpr _ h, f₁.gpr _ h])
    (by rw [f₄.rd, f₃.rd, f₂.rd, f₁.rd]) (by rw [f₄.wr, f₃.wr, f₂.wr, f₁.wr]) ?_ ?_
  · have e₃ : bytesAt s₄.mem (S + BitVec.ofNat 64 (A + 24)) 4 = toByte 0 4 := by
      rw [bytesAt_frame f₄.frame (hdj _ _ (by omega) (by omega) (by omega)) (by decide), f₃.bytes]
    have e₂ : bytesAt s₄.mem (S + BitVec.ofNat 64 (A + 20)) 4 = toByte idx 4 := by
      rw [bytesAt_frame f₄.frame (hdj _ _ (by omega) (by omega) (by omega)) (by decide),
        bytesAt_frame f₃.frame (hdj _ _ (by omega) (by omega) (by omega)) (by decide), f₂.bytes]
    have e₁ : bytesAt s₄.mem (S + BitVec.ofNat 64 (A + 16)) 4 = toByte 1 4 := by
      rw [bytesAt_frame f₄.frame (hdj _ _ (by omega) (by omega) (by omega)) (by decide),
        bytesAt_frame f₃.frame (hdj _ _ (by omega) (by omega) (by omega)) (by decide),
        bytesAt_frame f₂.frame (hdj _ _ (by omega) (by omega) (by omega)) (by decide), f₁.bytes]
    simp only [List.append_assoc]
    rw [bytesAt_split4, show A + 16 + 4 = A + 20 by omega, show A + 16 + 8 = A + 24 by omega,
      show A + 16 + 12 = A + 28 by omega, f₄.bytes, e₁, e₂, e₃]
  · exact (f₁.frame.sub (hsub _ (by omega) (by omega))).trans ((f₂.frame.sub (hsub _ (by omega) (by omega))).trans
      ((f₃.frame.sub (hsub _ (by omega) (by omega))).trans (f₄.frame.sub (hsub _ (by omega) (by omega)))))

/-- `wfields_ok`, the block alone. -/
theorem wfields_ok' {p : Params} (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32)
    {s : State} {S : Addr} {idx : Nat} (hidx : idx < 2 ^ 32)
    (hbx : s.gpr .rbx = S) (h12 : s.gpr .r12 = BitVec.ofNat 64 idx)
    (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ s.wr) {Q : State → Prop}
    (k : ∀ s', (∀ g, g ≠ .rax → s'.gpr g = s.gpr g) → s'.rd = s.rd → s'.wr = s.wr →
      bytesAt s'.mem (at' S (Layout.laneB 0 + p.n + 16)) 16 =
        toByte 1 4 ++ toByte idx 4 ++ toByte 0 4 ++ toByte 0 4 →
      Frame [⟨at' S (Layout.laneB 0 + p.n + 16), 16⟩] s.mem s'.mem → Q s') :
    WP isa (.block (setField .rbx (Layout.laneB 0 + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 16) 1 ++
        setFieldR .rbx (Layout.laneB 0 + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 20) .r12 ++
        setField .rbx (Layout.laneB 0 + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 24) 0 ++
        setField .rbx (Layout.laneB 0 + (Impl.SlhDsa.X86_64.Shake.layout p).adrsOff + 28) 0)) s Q := by
  have h := wfields_ok (is := []) hn hidx hbx h12 hw fun s' a b c d e => WP.block_nil (k s' a b c d e)
  rwa [List.append_nil] at h

theorem T_shake {p : Params} (hf : p.family = .shake) (pk : List Byte) (a : Adrs) (M : List Byte) :
    T p pk a M = shake256 (pk ++ a ++ M) p.n := by
  simp only [T, hf, shakeAdrs]

/-- What `xmssPk` changes: `chFrame`, and the lanes `B` but their `PK.seed`
and `a16`. -/
def xFrame (p : Params) (S sp : Addr) (stack : Nat) : List Region :=
  chFrame p S sp stack ++ (List.range 4).map (fun k => ⟨at' S (Layout.laneB k + p.n + 16), Layout.strideB - p.n - 16⟩)

theorem xFrame_sub (p : Params) (S sp : Addr) (stack : Nat) :
    ∀ r ∈ xFrame p S sp stack, ∃ r' ∈ changes p S ++ [below sp stack], Region.Sub r r' := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact chFrame_sub p S sp stack r hr
  · simp only [List.mem_map, List.mem_range] at hr
    obtain ⟨c, hc, rfl⟩ := hr
    exact ⟨_, List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨c, List.mem_range.mpr hc, List.mem_cons_of_mem _ (List.mem_cons_self ..)⟩))),
      fun _ h => h⟩

theorem chFrame_xFrame (p : Params) (S sp : Addr) (stack : Nat) :
    ∀ r ∈ chFrame p S sp stack, ∃ r' ∈ xFrame p S sp stack, Region.Sub r r' :=
  fun r hr => ⟨r, List.mem_append_left _ hr, fun _ h => h⟩

/-- A part of `scratch` after the lanes `B` is outside `xFrame`. -/
theorem xFrame_disj {p : Params} (hn : p.n ≤ 32) {S sp : Addr} {stack : Nat}
    (hstk : (below sp stack).Disjoint ⟨S, 2 ^ 16⟩) {o l : Nat} (h₁ : 12640 ≤ o) (h₂ : o + l ≤ 2 ^ 16) :
    ∀ r ∈ xFrame p S sp stack, Region.Disjoint ⟨at' S o, l⟩ r := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact chFrame_disj hn hstk (by omega) h₂ r hr
  · simp only [List.mem_map, List.mem_range] at hr
    obtain ⟨c, hc, rfl⟩ := hr
    exact Offset.disjoint S (by simp only [Layout.laneB, Layout.oB, Layout.strideB]; omega) (by omega)
      (by simp only [Layout.laneB, Layout.oB, Layout.strideB]; omega)

/-- A region outside `scratch` and the stack is outside `xFrame`. -/
theorem xFrame_disj' {p : Params} (hn : p.n ≤ 32) {S sp : Addr} {stack : Nat} {R : Region}
    (h₁ : R.Disjoint ⟨S, 2 ^ 16⟩) (h₂ : R.Disjoint (below sp stack)) :
    ∀ r ∈ xFrame p S sp stack, R.Disjoint r := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact chFrame_disj' hn h₁ h₂ r hr
  · simp only [List.mem_map, List.mem_range] at hr
    obtain ⟨c, hc, rfl⟩ := hr
    exact h₁.sub_right (Offset.sub_base S (by simp only [Layout.laneB, Layout.oB, Layout.strideB]; omega))

/-- The registers frame 1 saves are outside `xFrame`. -/
theorem xFrame_save {p : Params} (hn : p.n ≤ 32) {S sp : Addr} {stack : Nat}
    (hstk : (below sp stack).Disjoint ⟨S, 2 ^ 16⟩) :
    ∀ r ∈ xFrame p S sp stack, Region.Disjoint ⟨at' S 2528, 48⟩ r := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · simp only [chFrame, List.mem_append, List.mem_cons, List.mem_map, List.mem_range, List.not_mem_nil,
      or_false] at hr
    rcases hr with ((rfl | rfl | rfl) | ⟨c, hc, rfl⟩) | rfl
    · exact Offset.disjoint_base S (by omega) (by omega)
    · exact Offset.disjoint S (by omega) (by omega) (by omega)
    · exact Offset.disjoint S (by rw [oVar10']; omega) (by omega) (by rw [oVar10']; omega)
    · exact Offset.disjoint S (by simp only [Layout.laneA, Layout.oA, Layout.strideA]; omega) (by omega)
        (by simp only [Layout.laneA, Layout.oA, Layout.strideA]; omega)
    · exact (hstk.sub_right (Offset.sub_base S (by omega))).symm
  · simp only [List.mem_map, List.mem_range] at hr
    obtain ⟨c, hc, rfl⟩ := hr
    exact Offset.disjoint S (by simp only [Layout.laneB, Layout.oB, Layout.strideB]; omega) (by omega)
      (by simp only [Layout.laneB, Layout.oB, Layout.strideB]; omega)

/-- `wotsPk`: with the chains' ends in lane 0 of `B`'s message, the WOTS⁺
public key of the key pair `idx` (`T_len` of the ends, at the address of
type `WOTS_PK`) in lane 0 of `A`'s message. -/
theorem wotsPk_ok {p : Params} {f : Impl.SlhDsa.X86_64.Shake.Fns} (T : Thash4Impl p.n) (ht : f.t4 = T.code)
    (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) (hfam : p.family = .shake)
    (hlB : p.n + 32 + p.len * p.n ≤ Layout.strideB)
    {stack : Nat} (hst : T.stack + 16 ≤ stack) (hs63 : stack < 2 ^ 63)
    {s : State} {S : Addr} {idx : Nat} {pkSeed a16 : List Byte} (hidx : idx < 2 ^ 32)
    (hbx : s.gpr .rbx = S) (h12 : s.gpr .r12 = BitVec.ofNat 64 idx)
    (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ s.wr) (hS : S.toNat + 2 ^ 16 ≤ 2 ^ 64)
    (hstk : (below (s.gpr .rsp) stack).Disjoint ⟨S, 2 ^ 16⟩) (henv : Env p s.mem S pkSeed a16)
    {Q : State → Prop}
    (k : ∀ s', (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      bytesAt s'.mem (at' S (Layout.laneA 0 + p.n + 32)) p.n =
        Spec.SlhDsa.T p pkSeed (adrsOf a16 1 idx 0 0) (bytesAt s.mem (at' S (Layout.laneB 0 + p.n + 32)) (p.len * p.n)) →
      Frame (xFrame p S (s.gpr .rsp) stack) s.mem s'.mem → Q s') :
    WP isa (Impl.SlhDsa.X86_64.Verify.wotsPk p f) s Q := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have hn8 : p.n % 8 = 0 := by omega_using [hn]
  have hb0 : Layout.laneB 0 = 3808 := rfl
  have ha0 : Layout.laneA 0 = 3296 := rfl
  have hsB : Layout.strideB = 2208 := rfl
  have hmsg : (Impl.SlhDsa.X86_64.Shake.layout p).msgOff = p.n + 32 := rfl
  unfold Impl.SlhDsa.X86_64.Verify.wotsPk
  -- the fields
  refine WP.seq (wfields_ok' hn hidx hbx h12 hw fun s₁ g₁ r₁ w₁ b₁ f₁ => ?_)
  have hb₁ : s₁.gpr .rbx = S := by rw [g₁ _ (by decide), hbx]
  have hsp₁ : s₁.gpr .rsp = s.gpr .rsp := g₁ _ (by decide)
  have F₁ : Frame (xFrame p S (s.gpr .rsp) stack) s.mem s₁.mem := f₁.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_append_right _ (List.mem_map.mpr ⟨0, List.mem_range.mpr (by decide), rfl⟩),
      Offset.sub S (by omega) (by rw [hsB]; omega)⟩
  have henv₁ := Env.of_frame hn32 henv (F₁.sub (xFrame_sub p S _ stack)) hstk
  have hw₁ : (⟨S, 2 ^ 16⟩ : Region) ∈ s₁.wr := by rw [w₁]; exact hw
  -- the call, on the lanes `B`
  rw [ht]
  refine WP.seq (lanes_ok (p := p) T f.t4name hn hst hs63 (o := Layout.oB) (st := Layout.strideB)
    (len := p.n + 32 + p.len * p.n) (Or.inr ⟨rfl, rfl⟩) (by omega_using []) (by
      rw [Nat.add_mod, Nat.add_mod p.n, hn8, Nat.mul_mod, hn8]; simp) hlB hb₁ hw₁ hS
    (by rw [hsp₁]; exact hstk) henv₁.rc fun s₂ r₂ w₂ g₂ o₂ _ f₂ => ?_)
  have hb₂ : s₂.gpr .rbx = S := by rw [g₂ _ (by decide), hb₁]
  have hw₂ : (⟨S, 2 ^ 16⟩ : Region) ∈ s₂.wr := by rw [w₂]; exact hw₁
  -- the copy into lane 0 of `A`
  rw [hmsg]
  refine WP.mono (Levels.copy_ok (S := S) (t := .rbx) (sr := .rbx) (by decide) (by decide) (a := 0) (b := 0)
    (d₁ := Layout.laneB 0 + (p.n + 32)) (d₂ := Layout.laneA 0 + (p.n + 32)) (p.n / 8) s₂
    (by rw [hb₂]; exact Levels.scr0 S) (by rw [hb₂]; exact Levels.scr0 S) hw₂ (by omega) (by omega) (by omega))
    fun s₃ ⟨g₃, r₃, w₃, c₃, f₃⟩ => ?_
  have e8 : 8 * (p.n / 8) = p.n := by omega_using [hn]
  refine k s₃ (fun r hr => ?_) (by rw [r₃, r₂, r₁]) (by rw [w₃, w₂, w₁]) ?_ ?_
  · have hra : r ≠ .rax := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [g₃ _ hra, g₂ r hr, g₁ _ hra]
  · have hcp : bytesAt s₃.mem (at' S (Layout.laneA 0 + p.n + 32)) p.n =
        bytesAt s₂.mem (at' S (Layout.laneB 0 + p.n + 32)) p.n := by
      simp only [bytesAt]
      refine List.map_congr_left fun i hi => ?_
      have := c₃ i (by have := List.mem_range.mp hi; omega)
      simp only [Nat.zero_add] at this
      rw [at', at', add_add, add_add]
      simp only [Nat.add_assoc] at this ⊢
      exact this
    rw [hcp]
    have o₀ := o₂ 0 (by decide)
    rw [show Layout.oB + Layout.strideB * 0 = Layout.laneB 0 from rfl] at o₀
    rw [o₀, T_shake hfam]
    refine congrArg (shake256 · p.n) ?_
    -- lane 0's message: `PK.seed`, `a16`, the fields, the ends
    have hends : bytesAt s₁.mem (at' S (Layout.laneB 0 + p.n + 32)) (p.len * p.n) =
        bytesAt s.mem (at' S (Layout.laneB 0 + p.n + 32)) (p.len * p.n) :=
      bytesAt_frame f₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint S (by omega) (by omega) (by omega))
        (by omega)
    rw [show p.n + 32 + p.len * p.n = p.n + (16 + (16 + p.len * p.n)) by omega, bytesAt_split2, bytesAt_split2,
      bytesAt_split2, show Layout.laneB 0 + p.n + 16 + 16 = Layout.laneB 0 + p.n + 32 by omega]
    rw [show S + BitVec.ofNat 64 (Layout.laneB 0) = at' S (Layout.laneB 0) from rfl, henv₁.seedB 0 (by decide),
      show S + BitVec.ofNat 64 (Layout.laneB 0 + p.n) = at' S (Layout.laneB 0 + p.n) from rfl,
      henv₁.adrsB 0 (by decide),
      show S + BitVec.ofNat 64 (Layout.laneB 0 + p.n + 16) = at' S (Layout.laneB 0 + p.n + 16) from rfl, b₁,
      show S + BitVec.ofNat 64 (Layout.laneB 0 + p.n + 32) = at' S (Layout.laneB 0 + p.n + 32) from rfl, hends]
    simp only [adrsOf, List.append_assoc]
  · rw [hsp₁] at f₂
    refine F₁.trans ((f₂.sub fun r hr => ?_).trans (f₃.sub fun r hr => ?_))
    · simp only [lanesOut, List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with ⟨c, hc, rfl⟩ | rfl | rfl | rfl
      · exact ⟨_, List.mem_append_right _ (List.mem_map.mpr ⟨c, List.mem_range.mpr hc, rfl⟩),
          Offset.sub S (by simp only [Layout.laneB]; omega)
            (by simp only [Layout.laneB, Layout.oB, Layout.strideB]; omega)⟩
      · exact ⟨_, List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_cons_self ..))),
          fun _ h => h⟩
      · exact ⟨_, List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
          (List.mem_cons_of_mem _ (List.mem_cons_self ..)))), fun _ h => h⟩
      · exact ⟨_, List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _)), fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr
      obtain ⟨r', hr', hs'⟩ := sub_ch hn32 S (s.gpr .rsp) stack (o := Layout.laneA 0 + (p.n + 32)) (l := p.n)
        (Or.inl ⟨0, by decide, by omega, by omega⟩)
      exact ⟨r', List.mem_append_left _ hr', by rw [e8, Nat.zero_add]; exact hs'⟩

end VG.Proof.SlhDsa.X86_64
