module

-- separate module: the function's correctness, which its constant-time proof (`ForsCT`) does not rebuild

public import VerifiedGarbage.Proof.SlhDsa.X86_64.ForsFront
public import VerifiedGarbage.Proof.SlhDsa.X86_64.ForsMain
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.SlhDsa.Lemmas

/-!
# SLH-DSA (SHAKE) on x86-64: `forsSign`, the public key and the whole function

`pkFors`: `T_k` of the roots, with the type `FORS_ROOTS`, to `oMsg`
(`pk_ok`); `forsSign` from `forsContract`'s precondition to its
postcondition (`fors_wp`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64.Fors

open VG VG.X86_64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.SlhDsa.X86_64 (Layout setField setFieldR copyWords)
open VG.Impl.SlhDsa.X86_64.Fors
open VG.Proof.SlhDsa (fld)

theorem laneB0 : Layout.laneB 0 = 3808 := rfl

/-- The fields of lane 0 of the lanes `B` for `T_k`: `FORS_ROOTS`, `kp`, 0, 0. -/
theorem pkFields_ok {p : Params} (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) {S : Addr} {t : State}
    (hbx : t.gpr .rbx = S) (hKP : (t.gpr .r12).toNat < 2 ^ 32) (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ t.wr) :
    WP isa (.block (setField .rbx (Layout.laneB 0 + (⟨p.n, p.len⟩ : Layout).adrsOff + 16) 4 ++
        setFieldR .rbx (Layout.laneB 0 + (⟨p.n, p.len⟩ : Layout).adrsOff + 20) .r12 ++
        setField .rbx (Layout.laneB 0 + (⟨p.n, p.len⟩ : Layout).adrsOff + 24) 0 ++
        setField .rbx (Layout.laneB 0 + (⟨p.n, p.len⟩ : Layout).adrsOff + 28) 0)) t fun t' =>
      (∀ g, g ≠ .rax → t'.gpr g = t.gpr g) ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧ t'.mxcsr = t.mxcsr ∧
      bytesAt t'.mem (at' S (Layout.laneB 0 + p.n + 16)) 16 =
        toByte 4 4 ++ (toByte (t.gpr .r12).toNat 4 ++ (toByte 0 4 ++ toByte 0 4)) ∧
      Frame [⟨at' S (Layout.laneB 0 + p.n + 16), 16⟩] t.mem t'.mem := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have hbase : ∀ d, t.gpr .rbx + BitVec.ofNat 64 d = at' S d := fun d => by rw [hbx]
  refine WP.mono_mx (by simp [Code.allInstrs_eq, instrs, setField, setFieldR, loadsMxcsr])
    (Q := fun t' => t'.mxcsr = t.mxcsr → _) ?_ fun _ h hm => h hm
  simp only [Layout.adrsOff, List.append_assoc]
  refine setField_ok (by decide) (by decide : 4 < 2 ^ 31) (by rw [hbase]; exact Levels.in_scr hw (by rw [laneB0]; omega_using [hn32]))
    fun t₁ f₁ => ?_
  have hb₁ : t₁.gpr .rbx = S := by rw [f₁.gpr _ (by decide), hbx]
  refine setFieldR_ok (r := .r12) (by decide) (by rw [f₁.gpr _ (by decide)]; exact hKP)
    (by rw [hb₁]; exact Levels.in_scr (by rw [f₁.wr]; exact hw) (by rw [laneB0]; omega_using [hn32])) fun t₂ f₂ => ?_
  have hb₂ : t₂.gpr .rbx = S := by rw [f₂.gpr _ (by decide), hb₁]
  refine setField_ok (by decide) (by decide : 0 < 2 ^ 31)
    (by rw [hb₂]; exact Levels.in_scr (by rw [f₂.wr, f₁.wr]; exact hw) (by rw [laneB0]; omega_using [hn32])) fun t₃ f₃ => ?_
  have hb₃ : t₃.gpr .rbx = S := by rw [f₃.gpr _ (by decide), hb₂]
  refine setField_ok (by decide) (by decide : 0 < 2 ^ 31)
    (by rw [hb₃]; exact Levels.in_scr (by rw [f₃.wr, f₂.wr, f₁.wr]; exact hw) (by rw [laneB0]; omega_using [hn32]))
    fun t₄ f₄ => WP.block_nil fun hmx => ?_
  simp only [hbx, hb₁, hb₂, hb₃] at f₁ f₂ f₃ f₄
  have b₁ := f₁.bytes
  have b₂ := f₂.bytes
  have b₃ := f₃.bytes
  have b₄ := f₄.bytes
  rw [f₁.gpr _ (by decide)] at b₂
  have hb16 : Layout.laneB 0 + p.n + 16 + 16 ≤ 2 ^ 16 := by rw [laneB0]; omega_using [hn32]
  refine ⟨fun g h => by rw [f₄.gpr _ h, f₃.gpr _ h, f₂.gpr _ h, f₁.gpr _ h], by rw [f₄.rd, f₃.rd, f₂.rd, f₁.rd],
    by rw [f₄.wr, f₃.wr, f₂.wr, f₁.wr], hmx, ?_, ?_⟩
  · rw [show (16 : Nat) = 4 + (4 + (4 + 4)) from rfl, bytesAt_split, bytesAt_split, bytesAt_split]
    rw [keep1 f₄.frame (.inl (by omega_using [])) (by omega_using [hb16]) (by omega_using [hb16]),
      keep1 f₃.frame (.inl (by omega_using [])) (by omega_using [hb16]) (by omega_using [hb16]),
      keep1 f₂.frame (.inl (by omega_using [])) (by omega_using [hb16]) (by omega_using [hb16]), b₁,
      keep1 f₄.frame (.inl (by omega_using [])) (by omega_using [hb16]) (by omega_using [hb16]),
      keep1 f₃.frame (.inl (by omega_using [])) (by omega_using [hb16]) (by omega_using [hb16]),
      show Layout.laneB 0 + p.n + 16 + 4 = Layout.laneB 0 + p.n + 20 by omega_using [], b₂,
      keep1 f₄.frame (.inl (by omega_using [])) (by omega_using [hb16]) (by omega_using [hb16]),
      show Layout.laneB 0 + p.n + 20 + 4 = Layout.laneB 0 + p.n + 24 by omega_using [], b₃,
      show Layout.laneB 0 + p.n + 24 + 4 = Layout.laneB 0 + p.n + 28 by omega_using [], b₄]
  · have sub : ∀ o, o + 4 ≤ 16 → ∀ r ∈ [(⟨at' S (Layout.laneB 0 + p.n + 16 + o), 4⟩ : Region)],
        ∃ r' ∈ [(⟨at' S (Layout.laneB 0 + p.n + 16), 16⟩ : Region)], Region.Sub r r' := fun o ho r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub S (by omega_using []) (by omega_using [ho])⟩
    have e2 : Layout.laneB 0 + p.n + 20 = Layout.laneB 0 + p.n + 16 + 4 := by omega_using []
    have e3 : Layout.laneB 0 + p.n + 24 = Layout.laneB 0 + p.n + 16 + 8 := by omega_using []
    have e4 : Layout.laneB 0 + p.n + 28 = Layout.laneB 0 + p.n + 16 + 12 := by omega_using []
    have fr₂ := f₂.frame; have fr₃ := f₃.frame; have fr₄ := f₄.frame
    rw [e2] at fr₂; rw [e3] at fr₃; rw [e4] at fr₄
    exact (f₁.frame.sub (by simpa using sub 0 (by decide))).trans ((fr₂.sub (sub 4 (by decide))).trans
      ((fr₃.sub (sub 8 (by decide))).trans (fr₄.sub (sub 12 (by decide)))))

/-- The bytes of `c` strings of `n` bytes. -/
theorem bytesAt_flat (m : Mem) (S : Addr) (o n : Nat) : ∀ c,
    bytesAt m (at' S o) (c * n) = (List.range c).flatMap fun t => bytesAt m (at' S (o + t * n)) n
  | 0 => by simp [bytesAt]
  | c + 1 => by
    rw [Nat.succ_mul, bytesAt_split, bytesAt_flat m S o n c, List.range_succ, List.flatMap_append, List.flatMap_singleton]

/-- Lane 0 of the lanes `B`: `PK.seed ‖ a16 ‖` its fields `‖` its message. -/
theorem laneB_bytes {p : Params} {m : Mem} {S : Addr} {pk a16 F16 M : List Byte} {L : Nat}
    (hE : Env p m S pk a16) (hf : bytesAt m (at' S (Layout.laneB 0 + p.n + 16)) 16 = F16)
    (hm : bytesAt m (at' S (Layout.laneB 0 + p.n + 32)) L = M) :
    bytesAt m (at' S (Layout.laneB 0)) (p.n + 32 + L) = pk ++ (a16 ++ F16) ++ M := by
  rw [show p.n + 32 + L = p.n + (16 + (16 + L)) by omega_using [], bytesAt_split, bytesAt_split, bytesAt_split,
    show Layout.laneB 0 + p.n + 16 + 16 = Layout.laneB 0 + p.n + 32 by omega_using [], hE.seedB 0 (by decide),
    hE.adrsB 0 (by decide), hf, hm, List.append_assoc, List.append_assoc]

theorem T_shake {p : Params} (hf : p.family = .shake) (pk : List Byte) (a : Adrs) (M : List Byte) :
    T p pk a M = Spec.Sha3.shake256 (pk ++ a ++ M) p.n := by
  simp only [T, hf, shakeAdrs]

/-- What `pkFors` changes. -/
abbrev pkW (n : Nat) (S sp : Addr) (stack : Nat) : List Region :=
  [⟨at' S (Layout.laneB 0 + n + 16), 16⟩, ⟨at' S Layout.oMsg, n⟩] ++
    ((List.range 4).map (fun k => (⟨at' S (laneAt Layout.oB Layout.strideB k + n + 32), n⟩ : Region)) ++
      [⟨S, 1600⟩, ⟨at' S 2368, 32⟩, below sp stack])

theorem pk_ok {p : Params} (T : Thash4Impl p.n) (name : String) (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32)
    (hf : p.family = .shake) {stack : Nat} (hst : T.stack + 8 ≤ stack) (hs63 : stack < 2 ^ 63) {S : Addr}
    {pkSeed a16 R : List Byte} {t : State} (hbx : t.gpr .rbx = S) (hKP : (t.gpr .r12).toNat < 2 ^ 32)
    (h15 : t.gpr .r15 = at' S Layout.oMsg) (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ t.wr) (hS : S.toNat + 2 ^ 16 ≤ 2 ^ 64)
    (hstk : (below (t.gpr .rsp) stack).Disjoint ⟨S, 2 ^ 16⟩) (hE : Env p t.mem S pkSeed a16) (hk : p.k ≤ 35)
    (hR : bytesAt t.mem (at' S (Layout.laneB 0 + p.n + 32)) (p.k * p.n) = R) :
    WP isa (pkFors ⟨p.n, p.len⟩ p.k name T.code) t fun t' =>
      Fix t t' ∧ Env p t'.mem S pkSeed a16 ∧
      bytesAt t'.mem (at' S Layout.oMsg) p.n = Spec.SlhDsa.T p pkSeed (fld a16 4 (t.gpr .r12).toNat 0 0) R ∧
      Frame (pkW p.n S (t.gpr .rsp) stack) t.mem t'.mem := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have hn8 : p.n % 8 = 0 := by omega_using [hn]
  have e8 : 8 * (p.n / 8) = p.n := by omega_using [hn]
  have hkn : p.k * p.n ≤ 35 * 32 := Nat.mul_le_mul hk hn32
  have hkn8 : p.k * p.n % 8 = 0 := by rw [Nat.mul_mod, hn8, Nat.mul_zero]
  have eM : Layout.oMsg = 30496 := rfl
  unfold pkFors
  refine WP.seq (WP.mono (pkFields_ok hn hbx hKP hw) fun t₁ ⟨g₁, r₁, w₁, mx₁, F₁, f₁⟩ => ?_)
  have k₁ : ∀ q, q < 2 ^ 16 → (q < Layout.laneB 0 + p.n + 16 ∨ Layout.laneB 0 + p.n + 32 ≤ q) →
      t₁.mem (at' S q) = t.mem (at' S q) := fun q hq h => keepS f₁ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact dS S (by omega_using [h]) (by omega_using [hq]) (by rw [laneB0]; omega_using [hn32])
  have hE₁ : Env p t₁.mem S pkSeed a16 := env_bytes hn32 hE fun q hq => k₁ q
    (by simp only [EnvB] at hq; omega_using [hq]) (by
      simp only [EnvB] at hq; rw [laneB0]; omega_using [hq, hn32])
  have hb₁ : t₁.gpr .rbx = S := by rw [g₁ _ (by decide), hbx]
  have hsp₁ : t₁.gpr .rsp = t.gpr .rsp := g₁ _ (by decide)
  have hlen : p.n + 32 + p.k * p.n ≤ 2208 := by omega_using [hkn, hn32]
  refine WP.seq (WP.mono (t4g_ok T name hn hst hs63 (o := Layout.oB) (st := Layout.strideB) (len := p.n + 32 + p.k * p.n)
    (.inr ⟨rfl, rfl⟩) (by omega_using []) (by omega_using [hn8, hkn8]) (by simp only [Layout.strideB]; omega_using [hlen])
    hb₁ (by rw [w₁]; exact hw) hS (by rw [hsp₁]; exact hstk) hE₁.rc) fun t₂ C => ?_)
  have hm : bytesAt t₁.mem (at' S (laneAt Layout.oB Layout.strideB 0)) (p.n + 32 + p.k * p.n) =
      pkSeed ++ fld a16 4 (t.gpr .r12).toNat 0 0 ++ R := by
    have hM : bytesAt t₁.mem (at' S (Layout.laneB 0 + p.n + 32)) (p.k * p.n) = R := by
      rw [← hR]; refine bytesAt_ext fun i hi => ?_; rw [Levels.add_add]
      exact k₁ _ (by rw [laneB0]; omega_using [hi, hkn, hn32]) (.inr (by omega_using []))
    rw [show laneAt Layout.oB Layout.strideB 0 = Layout.laneB 0 from rfl, laneB_bytes hE₁ F₁ hM]
    rfl
  have hout := C.out 0 (by decide)
  rw [hm, ← T_shake hf] at hout
  have hb₂ : t₂.gpr .rbx = S := by rw [C.cs _ (by simp [calleeSaved]), hb₁]
  have h15₂ : t₂.gpr .r15 = at' S Layout.oMsg := by rw [C.cs _ (by simp [calleeSaved]), g₁ _ (by decide), h15]
  refine WP.mono_mx (by simpa [Code.allInstrs_eq, instrs] using (copyWords_nm .r15 0 .rbx
      (Layout.laneB 0 + (⟨p.n, p.len⟩ : Layout).msgOff) ((⟨p.n, p.len⟩ : Layout).n / 8)))
    (Levels.copy_ok (S := S) (a := Layout.oMsg) (b := 0) (d₁ := Layout.laneB 0 + (p.n + 32)) (d₂ := 0) (by decide) (by decide)
      (p.n / 8) t₂ h15₂ (by rw [hb₂]; exact Levels.scr0 S) (by rw [C.wr, w₁]; exact hw)
      (by rw [laneB0]; omega_using [e8, hn32]) (by rw [eM]; omega_using [e8, hn32]) (by rw [eM, laneB0]; omega_using [e8, hn32]))
    fun t' ⟨g', r', w', c', f'⟩ mx' => ?_
  rw [e8, Nat.add_zero] at c' f'
  have hmsg : Layout.laneB 0 + p.n + 32 + p.n ≤ Layout.oMsg := by rw [laneB0, eM]; omega_using [hn32]
  refine ⟨⟨fun r hr => ?_, by rw [r', C.rd, r₁], by rw [w', C.wr, w₁], by rw [mx', C.mx, mx₁]⟩, ?_, ?_, ?_⟩
  · obtain ⟨h0, _⟩ := mem_cs hr
    rw [g' _ h0, C.cs r hr, g₁ _ h0]
  · refine env_bytes hn32 (env_bytes hn32 hE₁ fun q hq => keepS C.frame fun r hr => ?_) fun q hq => keepS f' fun r hr => ?_
    · simp only [EnvB] at hq
      simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with ⟨k, hk', rfl⟩ | rfl | rfl | rfl
      · exact dS S (by simp only [laneAt, Layout.oB, Layout.strideB]; omega_using [hq, hk', hn32]) (by omega_using [hq])
          (by simp only [laneAt, Layout.oB, Layout.strideB]; omega_using [hk', hn32])
      · exact Offset.disjoint_base S (by omega_using [hq]) (by omega_using [hq])
      · exact dS S (by omega_using [hq]) (by omega_using [hq]) (by decide)
      · rw [hsp₁]; exact (hstk.sub_right (Levels.sub_scr S (by omega_using [hq]))).symm
    · simp only [EnvB] at hq
      simp only [List.mem_singleton] at hr; subst hr
      exact dS S (by rw [eM]; omega_using [hq]) (by omega_using [hq]) (by rw [eM]; omega_using [hn32])
  · rw [← hout]
    refine bytesAt_ext fun i hi => ?_
    rw [Levels.add_add, c' i hi, Nat.zero_add, show laneAt Layout.oB Layout.strideB 0 + p.n + 32 = Layout.laneB 0 + (p.n + 32)
      from by simp only [laneAt, Layout.laneB]; omega_using [], ← Levels.add_add]
  · have m1 : ∀ x ∈ [(⟨at' S (Layout.laneB 0 + p.n + 16), 16⟩ : Region)], x ∈ pkW p.n S (t.gpr .rsp) stack := fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx; simp
    refine (f₁.mono m1).trans ((C.frame.mono fun x hx => ?_).trans (f'.mono fun x hx => ?_))
    · rw [hsp₁] at hx; exact List.mem_append_right _ hx
    · simp only [List.mem_singleton] at hx; subst hx; simp

/-! ## The signature's bytes -/

theorem bytesAt_addA (m : Mem) (A : Addr) (x y : Nat) :
    bytesAt m A (x + y) = bytesAt m A x ++ bytesAt m (A + BitVec.ofNat 64 x) y := by
  simp only [bytesAt, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply, BitVec.ofNat_add, BitVec.add_assoc]

/-- The bytes of `c` strings of `L` bytes from `A`. -/
theorem bytesAt_flatA (m : Mem) (A : Addr) (L : Nat) : ∀ c,
    bytesAt m A (c * L) = (List.range c).flatMap fun t => bytesAt m (A + BitVec.ofNat 64 (t * L)) L
  | 0 => by simp [bytesAt]
  | c + 1 => by
    rw [Nat.succ_mul, bytesAt_addA, bytesAt_flatA m A L c, List.range_succ, List.flatMap_append, List.flatMap_singleton]

/-- The signature the trees leave at `SG`: each tree's private key value,
then its authentication path. -/
theorem sig_eq {p : Params} (hn32 : p.n ≤ 32) {m : Mem} {SG : Addr} {md skSeed pkSeed a16 : List Byte} {kp : Nat}
    (h16 : a16.length = 16) (hkp : kp < 2 ^ 32) {ix : Nat → Nat}
    (hix : ∀ i < p.k, ix i = (base2b md p.a p.k).getD i 0)
    (skp : ∀ t' < p.k, ∀ j < p.n, m (SG + BitVec.ofNat 64 (t' * ((p.a + 1) * p.n) + j)) =
      skv p pkSeed a16 skSeed kp (t' * 2 ^ p.a + ix t') j)
    (auth : ∀ t' < p.k, ∀ r < p.a, bytesAt m (SG + BitVec.ofNat 64 (t' * ((p.a + 1) * p.n) + p.n + r * p.n)) p.n =
      node p skSeed pkSeed a16 kp (t' * 2 ^ (p.a - r) + sib (ix t') r) r) :
    bytesAt m SG (p.k * ((p.a + 1) * p.n)) = forsSign p md skSeed pkSeed (forsAdrs a16 kp) := by
  rw [bytesAt_flatA, forsSign_eq]
  refine flatMap_range_congr fun i hi => ?_
  rw [forsSigPart, ← hix i hi, show (p.a + 1) * p.n = p.n + p.a * p.n by rw [Nat.add_mul, Nat.one_mul, Nat.add_comm],
    bytesAt_addA m, bytesAt_flatA]
  congr 1
  · rw [forsSkGen, sk_adrs h16 kp hkp]
    refine bytesAt_eq_of (prf_length hn32 _ _ _) fun j hj => ?_
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, show p.n + p.a * p.n = (p.a + 1) * p.n by
      rw [Nat.add_mul, Nat.one_mul, Nat.add_comm], skp i hi j hj]
    rfl
  · refine flatMap_range_congr fun r hr => ?_
    rw [Levels.add_add, Levels.add_add, show p.n + p.a * p.n = (p.a + 1) * p.n by
      rw [Nat.add_mul, Nat.one_mul, Nat.add_comm], ← Nat.add_assoc]
    exact auth i hi r hr

/-! ## The whole function -/

/-- The parameter sets `forsSign` is proved for: the SHAKE sets' `n`, `a`
and `k`. -/
def FSet (p : Params) : Prop :=
  p.family = .shake ∧ ((p.n = 16 ∧ p.a = 12 ∧ p.k = 14) ∨ (p.n = 16 ∧ p.a = 6 ∧ p.k = 33) ∨
    (p.n = 24 ∧ p.a = 14 ∧ p.k = 17) ∨ (p.n = 24 ∧ p.a = 8 ∧ p.k = 33) ∨ (p.n = 32 ∧ p.a = 14 ∧ p.k = 22) ∨
    (p.n = 32 ∧ p.a = 9 ∧ p.k = 35))

theorem FSet.facts {p : Params} (h : FSet p) :
    p.family = .shake ∧ (p.n = 16 ∨ p.n = 24 ∨ p.n = 32) ∧ 6 ≤ p.a ∧ p.a ≤ 14 ∧ 1 ≤ p.k ∧ p.k ≤ 35 ∧
      p.k * p.a ≤ 315 ∧ p.k * 2 ^ p.a ≤ 2 ^ 32 := by
  obtain ⟨hf, h⟩ := h
  refine ⟨hf, ?_⟩
  obtain ⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂, h₃⟩ := h <;>
    (rw [h₁, h₂, h₃]; decide)

/-- What the prologue and the indices leave for the rest. -/
structure Front (p : Params) (stack : Nat) (σ : State) (S SG : Addr) (t₀ : State) : Prop where
  M : MC p stack S SG t₀
  r15 : t₀.gpr .r15 = at' S Layout.oMsg
  sp : t₀.gpr .rsp = σ.gpr .rsp
  r12 : t₀.gpr .r12 = σ.gpr .rdx
  rd : t₀.rd = σ.rd
  wr : t₀.wr = σ.wr
  mx : t₀.mxcsr = σ.mxcsr
  saved : ∀ i < 6, t₀.mem.readW (at' S (Layout.oSave 2 i)) 64 = σ.gpr (Impl.SlhDsa.X86_64.savedRegs.getD i .rbx)
  frame : Frame [⟨at' S (Layout.oSave 2 0), 48⟩, ⟨at' S Layout.oFidx, 320⟩, ⟨at' S (Layout.oVar 2 0), 40⟩] σ.mem t₀.mem

theorem sigLen_eq (p : Params) : p.forsSigLen = p.k * ((p.a + 1) * p.n) := by
  simp only [Params.forsSigLen]; rw [Nat.add_comm 1 p.a, Nat.mul_assoc]

/-- The prologue and the indices: the trees' loop's invariant before tree 0. -/
theorem front_ok {p : Params} (hp : FSet p) {stack : Nat} {σ : State} {S SG : Addr} {pkSeed a16 : List Byte}
    (hS : σ.gpr .rdi = S) (hG : σ.gpr .rsi = SG) (R : Regions stack σ S [] ⟨SG, p.forsSigLen⟩)
    (hE : Env p σ.mem S pkSeed a16) (hkp : (σ.gpr .rdx).toNat < 2 ^ 32) :
    WP isa (.block (pro ++ indices p.a p.k)) σ fun t₀ => Front p stack σ S SG t₀ ∧
      TL p stack S SG pkSeed a16 (bytesAt σ.mem (at' S Layout.oSkSeed) p.n) (ixv σ.mem S p.a) t₀ 0 t₀ := by
  obtain ⟨hf, hn, ha6, ha14, hk1, hk35, hka, -⟩ := hp.facts
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have eF : Layout.oFidx = 31328 := rfl
  have eD : Layout.oDigest = 30304 := rfl
  have eS : Layout.oSave 2 0 = 2656 := rfl
  have eV : Layout.oVar 2 0 = 2704 := rfl
  have hsc : scratchLen = 2 ^ 16 := rfl
  have hwS : (⟨S, 2 ^ 16⟩ : Region) ∈ σ.wr := by rw [R.wr_eq]; simp [scratchLen]
  have hL := sigLen_eq p
  refine WP.block_append (WP.mono (pro_ok (by rw [hS]; exact hwS)) fun t P => ?_)
  have hbx : t.gpr .rbx = S := P.bx.trans hS
  have hbp : t.gpr .rbp = at' S Layout.oDigest := by rw [P.bp, hS]
  have F₀ : Frame [⟨at' S (Layout.oSave 2 0), 48⟩] σ.mem t.mem := by rw [← hS]; exact P.frame
  have kd : ∀ q, q < 2 ^ 16 → 2704 ≤ q → t.mem (at' S q) = σ.mem (at' S q) := fun q hq h => keepS F₀ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact dS S (.inr (by omega_using [eS, h])) (by omega_using [hq]) (by omega_using [eS])
  refine WP.mono (indices_ok (S := S) ha14 hk35 (by omega_using [hka]) hbx hbp (by rw [P.wr]; exact hwS))
    fun u ⟨g, r, w, mx, fi, v0, v4, v1, f⟩ => ?_
  have hixv : ∀ i < p.k, ixv t.mem S p.a i = ixv σ.mem S p.a i := fun i hi => by
    have : i * p.a ≤ 315 := by have := Nat.mul_le_mul_right p.a (Nat.le_of_lt hi); omega_using [this, hka]
    simp only [ixv]
    rw [kd _ (by omega_using [eD, this]) (by omega_using [eD]), kd _ (by omega_using [eD, this]) (by omega_using [eD]),
      kd _ (by omega_using [eD, this]) (by omega_using [eD])]
  have F : Frame [⟨at' S (Layout.oSave 2 0), 48⟩, ⟨at' S Layout.oFidx, 320⟩, ⟨at' S (Layout.oVar 2 0), 40⟩] σ.mem u.mem :=
    (F₀.mono fun x hx => by simp only [List.mem_singleton] at hx; simp [hx]).trans
      (f.mono fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> simp)
  have ku : ∀ q, q < 2 ^ 16 → (q < 2656 ∨ 2744 ≤ q) → q < Layout.oFidx → u.mem (at' S q) = σ.mem (at' S q) :=
    fun q hq h h' => keepS F fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact dS S (by omega_using [eS, h]) (by omega_using [hq]) (by omega_using [eS])
      · exact dS S (.inl (by omega_using [h'])) (by omega_using [hq]) (by omega_using [eF])
      · exact dS S (by omega_using [eV, h]) (by omega_using [hq]) (by omega_using [eV])
  have gx : ∀ g', g' ≠ .rax → g' ≠ .rcx → u.gpr g' = t.gpr g' := g
  refine ⟨⟨⟨hf, hn, ha6, ha14, hk1, hk35, by rw [gx _ (by decide) (by decide), hbx],
    by rw [gx _ (by decide) (by decide), P.r12]; exact hkp, by rw [w, P.wr]; exact hwS,
    by rw [w, P.wr, R.wr_eq, ← hL]; simp, by have := R.out_fit; rw [← hL]; exact this,
    by rw [← hsc]; exact R.scr_fit, by rw [gx _ (by decide) (by decide), P.sp, ← hsc]; exact R.stk_scr,
    by rw [← hL]; exact R.out_scr, by rw [gx _ (by decide) (by decide), P.sp, ← hL]; exact R.stk_out.symm⟩,
    by rw [gx _ (by decide) (by decide), P.r15, hS], by rw [gx _ (by decide) (by decide), P.sp],
    by rw [gx _ (by decide) (by decide), P.r12], r.trans P.rd, w.trans P.wr, mx.trans P.mx, fun i hi => ?_, F⟩,
    ⟨fun _ _ _ => rfl, rfl, rfl, rfl, ?_, ?_, by rw [v0]; rfl, ?_, ?_, fun i hi => by rw [fi i hi, hixv i hi],
      fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _),
      fun _ h => absurd h (Nat.not_lt_zero _), Frame.refl _ _⟩⟩
  · rw [keepSW f fun r hr => ?_, ← hS]
    · exact P.saved i hi
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dS S (.inl (by rw [oSave2]; omega_using [hi, eF])) (by rw [oSave2]; omega_using [hi]) (by omega_using [eF])
      · exact dS S (.inl (by rw [oSave2]; omega_using [hi, eV])) (by rw [oSave2]; omega_using [hi]) (by omega_using [eV])
  · exact env_bytes hn32 hE fun q hq => ku q (by simp only [EnvB] at hq; omega_using [hq])
      (by simp only [EnvB] at hq; omega_using [hq]) (by simp only [EnvB] at hq; omega_using [hq, eF])
  · exact sk_bytes (show SkAt p σ.mem S _ from rfl) fun q h₁ h₂ => ku q (by omega_using [h₂, hn32])
      (.inr (by omega_using [h₁])) (by omega_using [h₂, hn32, eF])
  · rw [v1, P.r14, hG, Nat.zero_mul]; exact (BitVec.add_zero _).symm
  · rw [v4, Nat.zero_mul]; rfl

/-- What `forsContract` lets `forsSign` change, from the parts. -/
theorem frame_all {p : Params} (hn32 : p.n ≤ 32) {stack : Nat} {S SG sp : Addr} {m₀ m₁ m₂ m₃ : Mem}
    (f₀ : Frame [⟨at' S (Layout.oSave 2 0), 48⟩, ⟨at' S Layout.oFidx, 320⟩, ⟨at' S (Layout.oVar 2 0), 40⟩] m₀ m₁)
    (f₁ : Frame (treeW p S SG sp stack) m₁ m₂) (f₂ : Frame (pkW p.n S sp stack) m₂ m₃) :
    Frame (changes p S ++ [⟨SG, p.forsSigLen⟩, below sp stack]) m₀ m₃ := by
  have eLA : ∀ k, Layout.laneA k = 3296 + 128 * k := fun _ => rfl
  have eLB : ∀ k, Layout.laneB k = 3808 + 2208 * k := fun _ => rfl
  have eAt : ∀ k, laneAt Layout.oB Layout.strideB k = 3808 + 2208 * k := fun _ => rfl
  have eVs : Layout.oVars = 2400 := rfl
  have eS : Layout.oSave 2 0 = 2656 := rfl
  have eV : Layout.oVar 2 0 = 2704 := rfl
  have e4 : Layout.oFrame 4 = 2912 := rfl
  have hsA : Layout.strideA = 128 := rfl
  have hsB : Layout.strideB = 2208 := rfl
  have mC : ∀ r ∈ changes p S, r ∈ changes p S ++ [⟨SG, p.forsSigLen⟩, below sp stack] := fun r h => List.mem_append_left _ h
  have mVs : (⟨at' S Layout.oVars, 768⟩ : Region) ∈ changes p S := by simp [changes]
  have mA : ∀ k < 4, (⟨at' S (Layout.laneA k + p.n + 16), Layout.strideA - p.n - 16⟩ : Region) ∈ changes p S :=
    fun k hk => by
      simp only [changes, List.mem_append, List.mem_flatMap, List.mem_range]
      exact .inl (.inr ⟨k, hk, by simp⟩)
  have mB : ∀ k < 4, (⟨at' S (Layout.laneB k + p.n + 16), Layout.strideB - p.n - 16⟩ : Region) ∈ changes p S :=
    fun k hk => by
      simp only [changes, List.mem_append, List.mem_flatMap, List.mem_range]
      exact .inl (.inr ⟨k, hk, by simp⟩)
  have sr : ∀ {r : Region}, r ∈ changes p S ++ [⟨SG, p.forsSigLen⟩, below sp stack] →
      ∃ R ∈ changes p S ++ [⟨SG, p.forsSigLen⟩, below sp stack], Region.Sub r R := fun h => ⟨_, h, fun _ h => h⟩
  have sV : ∀ {o l}, 2400 ≤ o → o + l ≤ 3168 →
      ∃ R ∈ changes p S ++ [⟨SG, p.forsSigLen⟩, below sp stack], Region.Sub ⟨at' S o, l⟩ R := fun h₁ h₂ =>
    ⟨_, mC _ mVs, Offset.sub S (by omega_using [eVs, h₁]) (by omega_using [eVs, h₂])⟩
  refine (f₀.sub fun r hr => ?_).trans ((f₁.sub fun r hr => ?_).trans (f₂.sub fun r hr => ?_))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact sV (by omega_using [eS]) (by omega_using [eS])
    · exact sr (mC _ (by simp [changes]))
    · exact sV (by omega_using [eV]) (by omega_using [eV])
  · simp only [List.mem_append, List.mem_cons, List.mem_map, List.mem_range, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | ⟨k, hk, rfl⟩
    · exact sr (mC _ (by simp [changes]))
    · exact sr (mC _ (by simp [changes]))
    · exact sV (by omega_using [eV]) (by omega_using [eV])
    · exact sV (by omega_using [e4]) (by omega_using [e4])
    · exact sr (mC _ (by simp [changes]))
    · exact sr (mC _ (by simp [changes]))
    · exact ⟨_, mC _ (mB 0 (by decide)), Offset.sub S (by omega_using []) (by rw [hsB]; omega_using [hn32])⟩
    · exact ⟨⟨SG, p.forsSigLen⟩, by simp, Region.sub_prefix (by rw [sigLen_eq])⟩
    · exact sr (by simp)
    · exact ⟨_, mC _ (mA k hk), Region.sub_prefix (by rw [hsA]; omega_using [hn32])⟩
  · simp only [List.mem_append, List.mem_cons, List.mem_map, List.mem_range, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl) | ⟨k, hk, rfl⟩ | rfl | rfl | rfl
    · exact ⟨_, mC _ (mB 0 (by decide)), Region.sub_prefix (by rw [hsB]; omega_using [hn32])⟩
    · exact ⟨⟨at' S Layout.oMsg, 64⟩, mC _ (by simp [changes]), Region.sub_prefix (by omega_using [hn32])⟩
    · exact ⟨_, mC _ (mB k hk), Offset.sub S (by rw [eAt, eLB]; omega_using [])
        (by rw [eAt, eLB, hsB]; omega_using [hn32])⟩
    · exact sr (mC _ (by simp [changes]))
    · exact sr (mC _ (by simp [changes]))
    · exact sr (by simp)

/-- A word of frame 2's saved registers is apart from what the trees and
`pkFors` change. -/
theorem save_disj {p : Params} (hn32 : p.n ≤ 32) {S SG sp : Addr} {stack q : Nat} (h₀ : 2656 ≤ q) (h₁ : q + 8 ≤ 2704)
    (dG : Region.Disjoint ⟨at' S q, 8⟩ ⟨SG, p.k * ((p.a + 1) * p.n)⟩)
    (dB : Region.Disjoint ⟨at' S q, 8⟩ (below sp stack)) :
    (∀ r ∈ treeW p S SG sp stack, Region.Disjoint ⟨at' S q, 8⟩ r) ∧
      ∀ r ∈ pkW p.n S sp stack, Region.Disjoint ⟨at' S q, 8⟩ r := by
  have d0 : Region.Disjoint ⟨at' S q, 8⟩ ⟨S, 1600⟩ := Offset.disjoint_base S (by omega_using [h₀]) (by omega_using [h₁])
  refine ⟨fun r hr => ?_, fun r hr => ?_⟩
  · simp only [List.mem_append, List.mem_cons, List.mem_map, List.mem_range, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | ⟨k, hk, rfl⟩
    · exact d0
    · exact dS S (.inr (by omega_using [h₀])) (by omega_using [h₁]) (by decide)
    · exact dS S (.inl (by rw [show Layout.oVar 2 0 = 2704 from rfl]; omega_using [h₁])) (by omega_using [h₁]) (by decide)
    · exact dS S (.inl (by rw [show Layout.oFrame 4 = 2912 from rfl]; omega_using [h₁])) (by omega_using [h₁]) (by decide)
    · exact dS S (.inl (by rw [show Layout.oN = 12640 from rfl]; omega_using [h₁])) (by omega_using [h₁]) (by decide)
    · exact dS S (.inl (by rw [show Layout.oRoots = 29280 from rfl]; omega_using [h₁])) (by omega_using [h₁]) (by decide)
    · exact dS S (.inl (by rw [laneB0]; omega_using [h₁])) (by omega_using [h₁]) (by rw [laneB0]; omega_using [hn32])
    · exact dG
    · exact dB
    · exact dS S (.inl (by rw [show Layout.laneA k = 3296 + 128 * k from rfl]; omega_using [h₁]))
        (by omega_using [h₁]) (by rw [show Layout.laneA k = 3296 + 128 * k from rfl]; omega_using [hk, hn32])
  · simp only [List.mem_append, List.mem_cons, List.mem_map, List.mem_range, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl) | ⟨k, hk, rfl⟩ | rfl | rfl | rfl
    · exact dS S (.inl (by rw [laneB0]; omega_using [h₁])) (by omega_using [h₁]) (by rw [laneB0]; omega_using [hn32])
    · exact dS S (.inl (by rw [show Layout.oMsg = 30496 from rfl]; omega_using [h₁])) (by omega_using [h₁])
        (by rw [show Layout.oMsg = 30496 from rfl]; omega_using [hn32])
    · exact dS S (.inl (by simp only [laneAt, Layout.oB, Layout.strideB]; omega_using [h₁])) (by omega_using [h₁])
        (by simp only [laneAt, Layout.oB, Layout.strideB]; omega_using [hk, hn32])
    · exact d0
    · exact dS S (.inr (by omega_using [h₀])) (by omega_using [h₁]) (by decide)
    · exact dB

/-- After the trees: `T_k` of the roots, the epilogue, and the
postcondition. -/
theorem fin_ok {p : Params} (hp : FSet p) (T : Thash4Impl p.n) (name : String) {stack : Nat}
    (hst : T.stack + 24 ≤ stack) (hs63 : stack < 2 ^ 63) {σ : State} {S SG : Addr} {pkSeed a16 : List Byte}
    (hS : σ.gpr .rdi = S) (hG : σ.gpr .rsi = SG) (R : Regions stack σ S [] ⟨SG, p.forsSigLen⟩)
    (hE : Env p σ.mem S pkSeed a16) {t₀ t₁ : State} (F : Front p stack σ S SG t₀)
    (H : TL p stack S SG pkSeed a16 (bytesAt σ.mem (at' S Layout.oSkSeed) p.n) (ixv σ.mem S p.a) t₀ p.k t₁) :
    WP isa (.seq (pkFors ⟨p.n, p.len⟩ p.k name T.code) (.block (Impl.SlhDsa.X86_64.restoreRegs 2))) t₁ fun s' =>
      abiPreserved σ s' ∧ (forsContract p stack).post σ s' := by
  obtain ⟨hf, hn, ha6, ha14, -, hk35, -, hk2⟩ := hp.facts
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have M := F.M
  have eS : Layout.oSave 2 0 = 2656 := rfl
  have eT : Layout.oSigTmp = 31648 := rfl
  have eD : Layout.oDigest = 30304 := rfl
  have hL := sigLen_eq p
  have c₁ : ∀ r, r ∈ calleeSaved → r ≠ .r13 → t₁.gpr r = t₀.gpr r := H.cs
  have hb₁ : t₁.gpr .rbx = S := by rw [c₁ _ (by simp [calleeSaved]) (by decide), M.bx]
  have h12 : t₁.gpr .r12 = σ.gpr .rdx := by rw [c₁ _ (by simp [calleeSaved]) (by decide), F.r12]
  have h15 : t₁.gpr .r15 = at' S Layout.oMsg := by rw [c₁ _ (by simp [calleeSaved]) (by decide), F.r15]
  have hsp₁ : t₁.gpr .rsp = σ.gpr .rsp := by rw [c₁ _ (by simp [calleeSaved]) (by decide), F.sp]
  have hw₁ : (⟨S, 2 ^ 16⟩ : Region) ∈ t₁.wr := by rw [H.wr]; exact M.w
  have hkp : (σ.gpr .rdx).toNat < 2 ^ 32 := by rw [← F.r12]; exact M.kp
  have h16 : a16.length = 16 := by rw [← hE.adrsA 0 (by decide)]; exact bytesAt_length' _ _ _
  -- a part of `scratch` below `oSigTmp` is apart from the signature and the stack
  have dG : ∀ {o l}, o + l ≤ Layout.oSigTmp →
      Region.Disjoint ⟨at' S o, l⟩ ⟨SG, p.k * ((p.a + 1) * p.n)⟩ := fun h =>
    (M.Gd.sub_right (Offset.sub_base S h)).symm
  have dB : ∀ {o l}, o + l ≤ 2 ^ 16 → Region.Disjoint ⟨at' S o, l⟩ (below (σ.gpr .rsp) stack) := fun h => by
    rw [← F.sp]; exact (M.stk.sub_right (Levels.sub_scr S h)).symm
  refine WP.seq (WP.mono (pk_ok T name hn hf (by omega_using [hst]) hs63 hb₁ (by rw [h12]; exact hkp) h15 hw₁ M.fit
    (by rw [hsp₁, ← F.sp]; exact M.stk) H.env hk35 (bytesAt_flat t₁.mem S (Layout.laneB 0 + p.n + 32) p.n p.k))
    fun t₂ ⟨X, hE₂, hpk, f₂⟩ => ?_)
  rw [hsp₁] at f₂
  have F₁ := H.frame
  rw [F.sp] at F₁
  have hb₂ : t₂.gpr .rbx = S := by rw [X.cs _ (by simp [calleeSaved]), hb₁]
  have hsv : ∀ i < 6, t₂.mem.readW (at' S (Layout.oSave 2 i)) 64 = σ.gpr (Impl.SlhDsa.X86_64.savedRegs.getD i .rbx) :=
    fun i hi => by
      have h₁ : 2656 + 8 * i + 8 ≤ 2704 := by omega_using [hi]
      obtain ⟨d₁, d₂⟩ := save_disj hn32 (q := 2656 + 8 * i) (by omega_using []) h₁ (dG (by rw [eT]; omega_using [h₁]))
        (dB (by omega_using [h₁]))
      rw [oSave2, keepSW f₂ d₂, keepSW F₁ d₁, ← oSave2]; exact F.saved i hi
  refine restore_ok (σ := σ) (S := S) hb₂ (by rw [X.wr]; exact hw₁) hsv (by rw [X.cs _ (by simp [calleeSaved]), hsp₁])
    fun t' hm hmx hrd hwr hcs => ?_
  have hF : Frame (changes p S ++ [⟨SG, p.forsSigLen⟩, below (σ.gpr .rsp) stack]) σ.mem t'.mem := by
    rw [hm]; exact frame_all hn32 F.frame F₁ f₂
  refine ⟨⟨hcs, hF.readW (r := retR σ) (Region.contains_self _ _) (fun r hr => ?_) (by decide),
    by rw [hmx, X.mx, H.mx, F.mx]⟩, ?_⟩
  · rcases List.mem_append.mp hr with hr | hr
    · have hsc : Region.Sub ⟨S, Layout.oSigTmp⟩ ⟨S, scratchLen⟩ := by
        have hs := Offset.sub_base S (d := 0) (n := Layout.oSigTmp) (k := scratchLen) (by rw [eT]; decide)
        rwa [← Levels.scr0 S] at hs
      exact R.ret_scr.sub_right fun x h' => hsc x (Levels.changes_low hn32 S r hr x h')
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact R.ret_out
      · exact Offset.base_disjoint_below _ (by omega_using [hs63])
  intro pk' a' sk' hE' hsk'
  dsimp only
  rw [hS] at hE' hsk' ⊢
  rw [hG]
  obtain rfl : pkSeed = pk' := by rw [← hE'.seedA 0 (by decide), hE.seedA 0 (by decide)]
  obtain rfl : a16 = a' := by rw [← hE'.adrsA 0 (by decide), hE.adrsA 0 (by decide)]
  unfold SkAt at hsk'
  subst hsk'
  have hix : ∀ i < p.k, ixv σ.mem S p.a i = (base2b (mdAt p σ.mem S) p.a p.k).getD i 0 := fun i hi => by
    have hlen : (mdAt p σ.mem S).length = (p.k * p.a + 7) / 8 := bytesAt_length' _ _ _
    have hia : i * p.a + p.a ≤ p.k * p.a := by
      have := Nat.mul_le_mul_right p.a (show i + 1 ≤ p.k by omega_using [hi]); rw [Nat.succ_mul] at this; exact this
    have gd : ∀ j, j < (p.k * p.a + 7) / 8 → (σ.mem (at' S (Layout.oDigest + j))).toNat =
        ((mdAt p σ.mem S).getD j 0).toNat := fun j hj => by
      rw [mdAt, bytesAt_getD _ _ (show j < p.mdLen from hj), Levels.add_add]
    refine (index_eq hlen ha14 hi (gd _ (by omega_using [hia, ha6])) (fun h => gd _ (by rw [hlen] at h; exact h))
      (fun h => gd _ (by rw [hlen] at h; exact h)) (BitVec.isLt _) (BitVec.isLt _)).symm
  have hskp := H.skp
  have hauth := H.auth
  have hroots := H.roots
  rw [F.r12] at hskp hauth hroots
  refine ⟨by rw [hm]; exact hE₂, ?_, ?_, hF⟩
  · rw [hm, hL, bytesAt_frame f₂ (fun r hr => ?_) (by omega_using [M.Gf])]
    · exact sig_eq hn32 h16 hkp hix hskp hauth
    · simp only [List.mem_append, List.mem_cons, List.mem_map, List.mem_range, List.not_mem_nil, or_false] at hr
      rcases hr with (rfl | rfl) | ⟨k, hk, rfl⟩ | rfl | rfl | rfl
      · exact (dG (by rw [laneB0, eT]; omega_using [hn32])).symm
      · exact (dG (by rw [show Layout.oMsg = 30496 from rfl, eT]; omega_using [hn32])).symm
      · exact (dG (by simp only [laneAt, Layout.oB, Layout.strideB]; rw [eT]; omega_using [hk, hn32])).symm
      · exact M.Gd.sub_right (Region.sub_prefix (by rw [eT]; omega_using []))
      · exact (dG (by rw [eT]; omega_using [])).symm
      · rw [← F.sp]; exact M.Gs
  · rw [hm, hpk, forsPkFromSig_forsSign hn32 hk2 _ _ _ (forsAdrs_length h16 _), roots_adrs h16 _ hkp, h12]
    exact congrArg (Spec.SlhDsa.T p pkSeed _) (flatMap_range_congr fun i hi => hroots i hi)

/-- `forsSign`, from `forsContract`'s precondition: its postcondition, with
the calling convention kept. -/
theorem fors_wp {p : Params} (hp : FSet p) (T : Thash4Impl p.n) (name ln : String) {stack : Nat}
    (hst : T.stack + 24 ≤ stack) (hs63 : stack < 2 ^ 63) {σ : State} (hpre : (forsContract p stack).pre σ) :
    WP isa (Impl.SlhDsa.X86_64.Fors.forsSign ⟨p.n, p.len⟩ p.a p.k name ln T.code) σ fun s' =>
      abiPreserved σ s' ∧ (forsContract p stack).post σ s' := by
  obtain ⟨R, ⟨pkSeed, a16, hE⟩, hkp⟩ := hpre
  obtain ⟨-, -, -, -, hk1, -, -, -⟩ := hp.facts
  generalize hS : σ.gpr .rdi = S at R hE
  generalize hG : σ.gpr .rsi = SG at R
  unfold Impl.SlhDsa.X86_64.Fors.forsSign
  refine WP.seq (WP.mono (front_ok hp hS hG R hE hkp) fun t₀ ⟨F, I⟩ => ?_)
  refine WP.seq (WP.mono (trees_ok T name ln hst hs63 F.M (fun i _ => Nat.mod_lt _ (Nat.two_pow_pos _))
    (tt := 0) hk1 (Nat.zero_add _) I) fun t₁ H => ?_)
  exact fin_ok hp T name hst hs63 hS hG R hE F H

/-! ## The stack pointer, the depth of calls, and calls of `forsSign` -/

theorem mulN_eq (n : Nat) : Impl.SlhDsa.X86_64.Wots.mulN n .rdx .rcx =
      [.mov .rcx (.reg .rdx), .shift .shl .rdx 4, .shift .shl .rcx 3, .alu .add .rdx (.reg .rcx)] ∨
    Impl.SlhDsa.X86_64.Wots.mulN n .rdx .rcx = [.shift .shl .rdx (if n = 16 then 4 else 5)] := by
  unfold Impl.SlhDsa.X86_64.Wots.mulN; split
  · exact .inl rfl
  · exact .inr rfl

theorem nosp_loop {b : Prog isa} {c : Cond} (h : NoSp b) : NoSp (.loop b c) := fun i hi => h i hi

section Nosp
variable (L : Impl.SlhDsa.X86_64.Layout) (a k : Nat) (name ln : String) {t4 : Prog isa} (hT : NoSp t4)
  (hL : NoSp (Impl.SlhDsa.X86_64.Tree.levels L name t4))
include hT

theorem tc_nosp {o st len : Nat} : NoSp (Impl.SlhDsa.X86_64.thashCall L name t4 o st len) :=
  Levels.nosp_seq (Levels.nosp_block (by simp [Impl.SlhDsa.X86_64.thashArgs, Taint.clobbers, Taint.dstOf]))
    fun i hi => hT i hi

theorem leaf_nosp : NoSp (leafBody L a name t4) := by
  unfold leafBody
  refine Levels.nosp_seq (Levels.nosp_block ?_) (Levels.nosp_seq (tc_nosp L name hT)
    (Levels.nosp_seq (Levels.nosp_block ?_) (Levels.nosp_seq (tc_nosp L name hT) (Levels.nosp_block ?_))))
  · simp [var, leafAdrs, Impl.SlhDsa.X86_64.setField, Impl.SlhDsa.X86_64.setFieldR, copyWords,
      List.all_flatMap, Taint.clobbers, Taint.dstOf]
  · simp [var, captureSk, Impl.SlhDsa.X86_64.setField, List.all_flatMap, Taint.clobbers, Taint.dstOf]
  · rcases mulN_eq L.n with h | h <;> simp [h, var, copyWords, List.all_flatMap, Taint.clobbers, Taint.dstOf]

include hL

theorem sub_nosp : NoSp (subtreeBody L a name ln t4) := by
  unfold subtreeBody subtreeHeights
  refine Levels.nosp_seq (Levels.nosp_block ?_) (Levels.nosp_seq (nosp_loop (leaf_nosp L a name hT))
    (Levels.nosp_seq (Levels.nosp_seq (Levels.nosp_block ?_) (Levels.nosp_seq (fun i hi => hL i hi) (Levels.nosp_block ?_)))
      (Levels.nosp_block ?_)))
  · simp [var, Taint.clobbers, Taint.dstOf]
  · simp [var, Impl.SlhDsa.X86_64.Tree.setParams, Taint.clobbers, Taint.dstOf]
  · rcases mulN_eq L.n with h | h <;> simp [h, var, copyWords, List.all_flatMap, Taint.clobbers, Taint.dstOf]
  · simp [var, Taint.clobbers, Taint.dstOf]

omit hT in
theorem top_nosp : NoSp (topHeights L a name ln t4) := by
  unfold topHeights
  refine Levels.nosp_seq ?_ (Levels.nosp_block ?_)
  · split
    · exact Levels.nosp_seq (Levels.nosp_block (by
        simp [var, copyWords, Impl.SlhDsa.X86_64.Tree.setParams, List.all_flatMap, Taint.clobbers, Taint.dstOf]))
        fun i hi => hL i hi
    · exact Levels.nosp_block rfl
  · rcases mulN_eq L.n with h | h <;> simp [h, var, copyWords, List.all_flatMap, Taint.clobbers, Taint.dstOf]

theorem tree_nosp : NoSp (treeBody L a k name ln t4) := by
  unfold treeBody
  refine Levels.nosp_seq (Levels.nosp_block ?_) (Levels.nosp_seq (nosp_loop (sub_nosp L a name ln hT hL))
    (Levels.nosp_seq (top_nosp L a name ln hL) (Levels.nosp_block ?_)))
  · simp [var, fidx, fidxR, Taint.clobbers, Taint.dstOf]
  · simp [var, Taint.clobbers, Taint.dstOf]

/-- `forsSign` never writes `rsp` itself. -/
theorem fors_nosp : NoSp (Impl.SlhDsa.X86_64.Fors.forsSign L a k name ln t4) := by
  unfold Impl.SlhDsa.X86_64.Fors.forsSign pkFors
  refine Levels.nosp_seq (Levels.nosp_block ?_) (Levels.nosp_seq (nosp_loop (tree_nosp L a k name ln hT hL))
    (Levels.nosp_seq (Levels.nosp_seq (Levels.nosp_block ?_) (Levels.nosp_seq (tc_nosp L name hT) (Levels.nosp_block ?_)))
      (Levels.nosp_block ?_)))
  · simp [pro, indices, index, var, Impl.SlhDsa.X86_64.saveRegs, List.all_flatMap, Taint.clobbers, Taint.dstOf]
  · simp [Impl.SlhDsa.X86_64.setField, Impl.SlhDsa.X86_64.setFieldR, Taint.clobbers, Taint.dstOf]
  · simp [copyWords, List.all_flatMap, Taint.clobbers, Taint.dstOf]
  · simp [Impl.SlhDsa.X86_64.restoreRegs, Taint.clobbers, Taint.dstOf] <;> decide

end Nosp

theorem fors_depth (L : Impl.SlhDsa.X86_64.Layout) (a k : Nat) (name ln : String) (t4 : Prog isa) :
    (Impl.SlhDsa.X86_64.Fors.forsSign L a k name ln t4).depth = t4.depth + 2 := by
  have h₂ := Levels.levels_depth L name t4
  unfold Impl.SlhDsa.X86_64.Fors.forsSign treeBody subtreeBody leafBody subtreeHeights topHeights pkFors
  split <;> simp only [Impl.SlhDsa.X86_64.thashCall, Code.depth, h₂, Nat.zero_max, Nat.max_zero, Nat.max_self,
    Nat.max_eq_right (Nat.le_succ (t4.depth + 1)), Nat.max_eq_left (Nat.le_succ (t4.depth + 1))]

/-- `forsSign`, from its precondition: an execution to its postcondition that
keeps the calling convention. -/
theorem fors_correct {p : Params} (hp : FSet p) (T : Thash4Impl p.n) (name ln : String) {stack : Nat}
    (hst : T.stack + 24 ≤ stack) (hs63 : stack < 2 ^ 63) :
    ∀ s, (forsContract p stack).pre s → ∃ t s',
      Exec isa (Impl.SlhDsa.X86_64.Fors.forsSign ⟨p.n, p.len⟩ p.a p.k name ln T.code) s t s' ∧
      abiPreserved s s' ∧ (forsContract p stack).post s s' := fun s h => by
  obtain ⟨t, s', e, abi, post⟩ := fors_wp hp T name ln hst hs63 h
  exact ⟨t, s', e, abi, post⟩

theorem fors_nospT {p : Params} (hp : FSet p) (T : Thash4Impl p.n) (name ln : String) :
    NoSp (Impl.SlhDsa.X86_64.Fors.forsSign ⟨p.n, p.len⟩ p.a p.k name ln T.code) :=
  fors_nosp _ _ _ _ _ T.nosp (Levels.levels_nosp hp.facts.2.1 name T.nosp)

/-- A call of `forsSign`, given its precondition at the call's entry
(narrowed to the regions `rd` and `wr`). -/
theorem forscall_ok {p : Params} (hp : FSet p) (T : Thash4Impl p.n) (name ln fn : String) {stack : Nat}
    (hst : T.stack + 24 ≤ stack) (hs63 : stack < 2 ^ 63) {s : State}
    {rd wr : List Region} (hpre : (forsContract p stack).pre (s.callEntry.withRegions rd wr))
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame (wr ++ [below (s.gpr .rsp) (8 * (T.code.depth + 3))]) s.mem s'.mem →
      (∃ s₂ : State, s₂.mem = s'.mem ∧ (∀ r, r ≠ .rsp → s₂.gpr r = s'.gpr r) ∧
        (forsContract p stack).post (s.callEntry.withRegions rd wr) s₂) →
      s'.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10 → Q s') :
    WP isa (.call fn (Impl.SlhDsa.X86_64.Fors.forsSign ⟨p.n, p.len⟩ p.a p.k name ln T.code)) s Q := by
  have hd := T.depth_le
  exact WP.call_mx (fors_correct hp T name ln hst hs63) (fors_nospT hp T name ln)
    (by rw [fors_depth]; omega_using [hd]) hpre hc hw fun s' h₁ h₂ h₃ h₄ _ h₆ h₇ =>
      hQ s' h₁ h₂ h₃ (by rw [fors_depth] at h₄; exact h₄) h₆ h₇

/-! ## A state satisfying the precondition -/

/-- `levels`'s witness with the signature at `lAU`, for the key pair 0. -/
def forsSat (p : Params) : State where
  gpr r := match r with
    | .rdi => Levels.lS | .rsi => Levels.lAU | .rsp => Levels.lsp | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := Levels.lmem
  rd := []
  wr := [⟨Levels.lS, scratchLen⟩, ⟨Levels.lAU, p.forsSigLen⟩]

theorem forsSat_pre {p : Params} (hp : FSet p) {stack : Nat} (hs63 : stack < 2 ^ 63) :
    (forsContract p stack).pre (forsSat p) := by
  obtain ⟨-, hn, -, ha, -, hk35, -, -⟩ := hp.facts
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have hSL : p.forsSigLen ≤ 35 * 15 * 32 := by
    simp only [Params.forsSigLen]; exact Nat.mul_le_mul (Nat.mul_le_mul hk35 (by omega_using [ha])) hn32
  have hLA : ∀ k, Layout.laneA k = 3296 + 128 * k := fun _ => rfl
  have hLB : ∀ k, Layout.laneB k = 3808 + 2208 * k := fun _ => rfl
  have eT : Layout.oSigTmp = 31648 := rfl
  have hAs : Region.Disjoint ⟨Levels.lAU, p.forsSigLen⟩ ⟨Levels.lS, Layout.oSigTmp⟩ :=
    Offset.disjoint Levels.lsp (.inr (by rw [eT]; omega_using [])) (by omega_using [hSL]) (by rw [eT]; omega_using [])
  refine ⟨⟨rfl, rfl, by show Levels.lS.toNat + scratchLen ≤ 2 ^ 64; rw [Levels.lS_toNat]; decide, ?_, hAs,
    fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil, ?_, ?_,
    fun _ h => absurd h List.not_mem_nil, ?_, ?_, fun _ h => absurd h List.not_mem_nil⟩,
    ⟨List.replicate p.n 0, List.replicate 16 0, Levels.lsat_rc, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_,
      fun k hk => ?_⟩, by show (0 : BitVec 64).toNat < 2 ^ 32; decide⟩
  · show (Levels.lsp + BitVec.ofNat 64 0x200000).toNat + p.forsSigLen ≤ 2 ^ 64
    have : (Levels.lsp + BitVec.ofNat 64 0x200000).toNat = 2 ^ 63 + 0x200000 := by decide
    omega_using [this, hSL]
  · exact (Offset.disjoint_base Levels.lsp (k := 8) (by omega_using []) (by rw [show scratchLen = 65536 from rfl]; omega_using [])).symm
  · exact (Offset.disjoint_base Levels.lsp (k := 8) (by omega_using []) (by omega_using [hSL])).symm
  · exact (Offset.disjoint_below Levels.lsp (n := stack) (d := 0x100000) (k := scratchLen)
      (by rw [show scratchLen = 65536 from rfl]; omega_using [hs63])).symm
  · exact (Offset.disjoint_below Levels.lsp (n := stack) (d := 0x200000) (k := p.forsSigLen) (by omega_using [hs63, hSL])).symm
  · exact (Levels.lbytes_zero (by rw [hLA]; omega_using []) (by rw [hLA]; omega_using [hk, hn32]))
  · exact (Levels.lbytes_zero (by rw [hLB]; omega_using []) (by rw [hLB]; omega_using [hk, hn32]))
  · exact (Levels.lbytes_zero (by rw [hLA]; omega_using []) (by rw [hLA]; omega_using [hk, hn32]))
  · exact (Levels.lbytes_zero (by rw [hLB]; omega_using []) (by rw [hLB]; omega_using [hk, hn32]))

end VG.Proof.SlhDsa.X86_64.Fors
