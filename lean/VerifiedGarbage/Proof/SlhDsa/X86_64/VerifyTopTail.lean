module

-- separate module: the comparison and epilogue, one stage of the chain of verify's proof

public import VerifiedGarbage.Proof.SlhDsa.X86_64.VerifyTopLoop
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.X86_64.WordIOBytes
import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsBase
import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsCorrect
import VerifiedGarbage.Proof.SlhDsa.X86_64.WotsBlocks
import VerifiedGarbage.Proof.SlhDsa.X86_64.ForsLeaf
import VerifiedGarbage.Proof.SlhDsa.X86_64.KeyGen

/-!
# SLH-DSA (SHAKE) on x86-64, `verify`: the result

Untrusted: everything here is checked by Lean. The words of the root at
`oMsg` and of `PK.root` at `oPkRoot`, XORed and ORed together, are 0 if and
only if the two are equal (`cmp_ok`); then `verify`'s result and the
callee-saved registers restored (`tail_ok`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64.VerifyTop

open VG VG.X86_64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.SlhDsa.X86_64 (Layout savedRegs)
open VG.Impl.SlhDsa.X86_64.Shake (oKgSave kgRestore)
open VG.Impl.Sha3.X86_64 (at_)
open VG.Proof.Sha3.X86_64 (Upd wp_mov wp_movm wp_xorm wp_mov32i wp_test ea_at)

theorem or_eq_zero' {x y : BitVec 64} : x ||| y = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    constructor <;> (ext i hi; have := congrArg (fun z : BitVec 64 => z[i]) h; simp at this; simp [this])
  · rintro ⟨rfl, rfl⟩; simp

theorem xor_eq_zero' {x y : BitVec 64} : x ^^^ y = 0 ↔ x = y := by
  constructor
  · intro h; ext i hi; have := congrArg (fun z : BitVec 64 => z[i]) h; simp at this; exact this
  · rintro rfl; simp

theorem bytes8_eq (m : Mem) (A B : Addr) : bytesAt m A 8 = bytesAt m B 8 ↔ m.readW A 64 = m.readW B 64 := by
  constructor
  · intro h
    apply Proof.Bignum.X86_64.WordIO.eq_of_bytes
    intro j hj
    rw [← ForsCT.fbyte_readW64 m A hj, ← ForsCT.fbyte_readW64 m B hj]
    have := congrArg (fun l : List Byte => l[j]?) h
    simpa [bytesAt, hj] using this
  · intro h
    simp only [bytesAt]
    refine List.map_congr_left fun j hj => ?_
    have hj' := List.mem_range.mp hj
    rw [ForsCT.fbyte_readW64 m A hj', ForsCT.fbyte_readW64 m B hj', h]

theorem bytes_eq_words (m : Mem) (A B : Addr) : ∀ w, bytesAt m A (8 * w) = bytesAt m B (8 * w) ↔
    ∀ i < w, m.readW (A + BitVec.ofNat 64 (8 * i)) 64 = m.readW (B + BitVec.ofNat 64 (8 * i)) 64
  | 0 => by simp [bytesAt]
  | w + 1 => by
    rw [show 8 * (w + 1) = 8 * w + 8 by omega, KeyGen.bytesAt_add, KeyGen.bytesAt_add]
    have iff : bytesAt m A (8 * w) ++ bytesAt m (A + BitVec.ofNat 64 (8 * w)) 8 =
        bytesAt m B (8 * w) ++ bytesAt m (B + BitVec.ofNat 64 (8 * w)) 8 ↔
        bytesAt m A (8 * w) = bytesAt m B (8 * w) ∧
          bytesAt m (A + BitVec.ofNat 64 (8 * w)) 8 = bytesAt m (B + BitVec.ofNat 64 (8 * w)) 8 :=
      ⟨fun h => List.append_inj h (by rw [bytesAt_len, bytesAt_len]), fun ⟨h1, h2⟩ => by rw [h1, h2]⟩
    rw [iff, bytes_eq_words m A B w, bytes8_eq]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact h1 i hi
      · exact h2
    · intro h
      exact ⟨fun i hi => h i (by omega), h w (by omega)⟩

variable {L : VL} {g : Reg → BitVec 64} {m₀ : Mem}

/-- After `w` words of the comparison. -/
def CI (L : VL) (t₀ : State) (w : Nat) (t : State) : Prop :=
  (∀ r, r ≠ .rax → r ≠ .rcx → t.gpr r = t₀.gpr r) ∧ t.mem = t₀.mem ∧ t.rd = t₀.rd ∧ t.wr = t₀.wr ∧
    (t.gpr .rax = 0 ↔ ∀ i < w, t₀.mem.readW (at' L.S Layout.oMsg + BitVec.ofNat 64 (8 * i)) 64 =
      t₀.mem.readW (at' L.S Layout.oPkRoot + BitVec.ofNat 64 (8 * i)) 64)

theorem cmp_ok {p : Params} (hp : VPar p) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block (.mov32 .rax (.imm 0) :: (List.range (p.n / 8)).flatMap (fun w =>
        [.mov .rcx (.mem (at_ .rbx (Layout.oMsg + 8 * w))), .alu .xor .rcx (.mem (at_ .rbx (Layout.oPkRoot + 8 * w))),
          .alu .or .rax (.reg .rcx)]) ++ ([.alu .test .rax (.reg .rax)] : List Instr))) t fun t' =>
      Ctx L g m₀ t' ∧ t'.zf = some (decide (bytesAt t.mem (at' L.S Layout.oMsg) p.n =
        bytesAt t.mem (at' L.S Layout.oPkRoot) p.n)) := by
  have hn := hp.n
  rw [List.cons_append]
  refine wp_mov32i fun t₀ u₀ => ?_
  have step : ∀ w < p.n / 8, ∀ u, CI L t₀ w u → WP isa (.block [.mov .rcx (.mem (at_ .rbx (Layout.oMsg + 8 * w))),
      .alu .xor .rcx (.mem (at_ .rbx (Layout.oPkRoot + 8 * w))), .alu .or .rax (.reg .rcx)]) u (CI L t₀ (w + 1)) := by
    intro w hw u ⟨hg, hm, hr, hwr, hz⟩
    have hb : u.gpr .rbx = L.S := by rw [hg _ (by decide) (by decide), u₀.other _ (by decide), hc.rbx]
    have hin : ∀ {o : Nat}, o + 8 ≤ 65536 → InRegions (u.rd ++ u.wr) (L.S + BitVec.ofNat 64 o) 8 := fun h => by
      rw [hr, hwr, u₀.rd, u₀.wr]; exact Levels.in_scr' hc.inScr h
    refine wp_movm (by rw [ea_at, hb]) (hin (by simp only [show Layout.oMsg = 30496 from rfl]; omega)) fun u₁ v₁ =>
      wp_xorm (by rw [ea_at, v₁.other _ (by decide), hb])
        (by rw [v₁.rd, v₁.wr]; exact hin (by simp only [show Layout.oPkRoot = 3264 from rfl]; omega)) fun u₂ v₂ =>
      Fors.wp_orr fun u₃ v₃ => WP.block_nil ?_
    refine ⟨fun r h1 h2 => by rw [v₃.other _ h1, v₂.other _ h2, v₁.other _ h2, hg r h1 h2],
      by rw [v₃.mem, v₂.mem, v₁.mem, hm], by rw [v₃.rd, v₂.rd, v₁.rd, hr], by rw [v₃.wr, v₂.wr, v₁.wr, hwr], ?_⟩
    rw [v₃.gpr, v₂.other _ (by decide), v₁.other _ (by decide), v₂.gpr, v₁.gpr, v₁.mem, or_eq_zero', hz,
      xor_eq_zero', hm]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact h1 i hi
      · rw [Levels.at_add, Levels.at_add]; exact h2
    · intro h
      refine ⟨fun i hi => h i (by omega), ?_⟩
      have := h w (by omega); rwa [Levels.at_add, Levels.at_add] at this
  refine WP.block_append (M := isa) ?_
  refine WP.mono (KeyGen.wp_flatMap (P := CI L t₀) (p.n / 8)
    ⟨fun _ _ _ => rfl, rfl, rfl, rfl, by rw [u₀.gpr]; exact ⟨fun _ _ h => absurd h (by omega), fun _ => rfl⟩⟩ step)
    fun u ⟨hg, hm, hr, hwr, hz⟩ => Proof.Sha3.X86_64.wp_test fun u' g' m' r' w' z' => WP.block_nil ?_
  have hm₀ : t₀.mem = t.mem := u₀.mem
  refine ⟨hc.regs (by rw [r', hr, u₀.rd]) (by rw [w', hwr, u₀.wr]) (by rw [m', hm, hm₀]) fun r hr' => by
    rw [g', hg r (by intro e; subst e; revert hr'; decide) (by intro e; subst e; revert hr'; decide),
      u₀.other _ (by intro e; subst e; revert hr'; decide)], ?_⟩
  rw [z', BitVec.and_self]
  congr 1
  have e8 : 8 * (p.n / 8) = p.n := by omega
  have hw := bytes_eq_words t₀.mem (at' L.S Layout.oMsg) (at' L.S Layout.oPkRoot) (p.n / 8)
  rw [e8] at hw
  have key : u.gpr .rax = 0 ↔ bytesAt t.mem (at' L.S Layout.oMsg) p.n = bytesAt t.mem (at' L.S Layout.oPkRoot) p.n := by
    rw [← hm₀]; exact hz.trans hw.symm
  exact Bool.eq_iff_iff.mpr (by simp only [beq_iff_eq, decide_eq_true_eq]; exact key)

theorem restoreK_ok {σ t : State} {S : Addr} (hbx : t.gpr .rbx = S) (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ t.wr)
    (hsv : ∀ i < 6, t.mem.readW (at' S (oKgSave + 8 * i)) 64 = σ.gpr (savedRegs.getD i .rbx))
    (hsp : t.gpr .rsp = σ.gpr .rsp) {Q : State → Prop}
    (k : ∀ t', t'.mem = t.mem → t'.rd = t.rd → t'.wr = t.wr → (∀ r ∈ calleeSaved, t'.gpr r = σ.gpr r) →
      (∀ r, r ∉ calleeSaved → t'.gpr r = t.gpr r) → Q t') :
    WP isa (.block (kgRestore)) t Q := by
  have hin : ∀ (u : State), u.rd = t.rd → u.wr = t.wr → ∀ i < 6, InRegions (u.rd ++ u.wr) (at' S (oKgSave + 8 * i)) 8 :=
    fun u hr hw' i hi => by rw [hr, hw']; exact Levels.in_scr' hw (by rw [show oKgSave = 34080 from rfl]; omega)
  rw [show kgRestore = [Instr.mov .r15 (.mem (Impl.Sha3.X86_64.at_ .rbx (oKgSave + 8 * 5))),
    .mov .r14 (.mem (Impl.Sha3.X86_64.at_ .rbx (oKgSave + 8 * 4))), .mov .r13 (.mem (Impl.Sha3.X86_64.at_ .rbx (oKgSave + 8 * 3))),
    .mov .r12 (.mem (Impl.Sha3.X86_64.at_ .rbx (oKgSave + 8 * 2))), .mov .rbp (.mem (Impl.Sha3.X86_64.at_ .rbx (oKgSave + 8 * 1))),
    .mov .rbx (.mem (Impl.Sha3.X86_64.at_ .rbx (oKgSave + 8 * 0)))] from rfl]
  refine wp_movm (by rw [ea_at, hbx]) (hin t rfl rfl 5 (by decide)) fun t₁ u₁ => ?_
  refine wp_movm (by rw [ea_at, u₁.other _ (by decide), hbx]) (hin _ u₁.rd u₁.wr 4 (by decide)) fun t₂ u₂ => ?_
  refine wp_movm (by rw [ea_at, u₂.other _ (by decide), u₁.other _ (by decide), hbx])
    (hin _ (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr]) 3 (by decide)) fun t₃ u₃ => ?_
  refine wp_movm (by rw [ea_at, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hbx])
    (hin _ (by rw [u₃.rd, u₂.rd, u₁.rd]) (by rw [u₃.wr, u₂.wr, u₁.wr]) 2 (by decide)) fun t₄ u₄ => ?_
  refine wp_movm (by rw [ea_at, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hbx])
    (hin _ (by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]) (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]) 1 (by decide)) fun t₅ u₅ => ?_
  refine wp_movm (by rw [ea_at, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hbx])
    (hin _ (by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]) (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]) 0 (by decide))
    fun t₆ u₆ => WP.block_nil ?_
  have hm₁ : t₁.mem = t.mem := u₁.mem
  have hm₂ : t₂.mem = t.mem := by rw [u₂.mem, hm₁]
  have hm₃ : t₃.mem = t.mem := by rw [u₃.mem, hm₂]
  have hm₄ : t₄.mem = t.mem := by rw [u₄.mem, hm₃]
  have hm₅ : t₅.mem = t.mem := by rw [u₅.mem, hm₄]
  refine k t₆ (by rw [u₆.mem, hm₅]) (by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd])
    (by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]) (fun r hr => ?_) fun r hr => ?_
  rotate_left
  · have ne : ∀ q ∈ calleeSaved, r ≠ q := fun q hq e => hr (e ▸ hq)
    rw [u₆.other _ (ne _ (by decide)), u₅.other _ (ne _ (by decide)), u₄.other _ (ne _ (by decide)),
      u₃.other _ (ne _ (by decide)), u₂.other _ (ne _ (by decide)), u₁.other _ (ne _ (by decide))]
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [u₆.gpr, hm₅]; exact hsv 0 (by decide)
  · rw [u₆.other _ (by decide), u₅.gpr, hm₄]; exact hsv 1 (by decide)
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hsp]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, hm₃]; exact hsv 2 (by decide)
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, hm₂]
    exact hsv 3 (by decide)
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, hm₁]
    exact hsv 4 (by decide)
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.gpr]
    exact hsv 5 (by decide)

/-- What the frame's body leaves, with the result `v`. -/
structure TailPost (L : VL) (g : Reg → BitVec 64) (m₀ : Mem) (v : BitVec 32) (t : State) : Prop where
  rd : t.rd = L.rd
  wr : t.wr = L.FR :: [L.SCR]
  rsp : t.gpr .rsp = L.SP
  cs : ∀ r ∈ calleeSaved, r ≠ .rsp → t.gpr r = g r
  ret : (t.gpr .rax).setWidth 32 = v
  frame : Frame [L.SCR, L.STK] m₀ t.mem

theorem epi_ok {u : State} (hc : Ctx L g m₀ u) {v : BitVec 32} (hv : u.gpr .rax = v.setWidth 64) :
    WP isa (.block (.mov .r10 (.reg .rax) :: kgRestore ++ ([.mov .rax (.reg .r10)] : List Instr))) u (TailPost L g m₀ v) := by
  let σ : State := { u with gpr := fun r => if r = .rsp then L.SP else g r }
  refine wp_mov fun u₁ e₁ => ?_
  have hc₁ : Ctx L g m₀ u₁ := hc.regs e₁.rd e₁.wr e₁.mem fun r hr => e₁.other r (by
    intro e; subst e; revert hr; decide)
  refine WP.block_append (restoreK_ok (σ := σ) hc₁.rbx hc₁.inScr (fun i hi => by
      rw [hc₁.saved i hi]
      have : savedRegs.getD i .rbx ≠ .rsp := by
        rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega) with rfl | rfl | rfl | rfl | rfl | rfl <;>
          decide
      show _ = (if savedRegs.getD i .rbx = .rsp then L.SP else g _)
      simp only [this, ↓reduceIte]) (by simp [σ, hc₁.rsp]) fun u₂ m₂ r₂ w₂ c₂ o₂ => ?_)
  refine wp_mov fun u₃ e₃ => WP.block_nil ?_
  have hcs : ∀ r ∈ calleeSaved, u₃.gpr r = σ.gpr r := fun r hr => by
    rw [e₃.other _ (by intro e; subst e; revert hr; decide), c₂ r hr]
  refine ⟨by rw [e₃.rd, r₂, hc₁.rd], by rw [e₃.wr, w₂, hc₁.wr], by rw [hcs .rsp (by decide)]; simp [σ],
    fun r hr h => by rw [hcs r hr]; simp [σ, h], ?_, ?_⟩
  · have h10 : u₂.gpr .r10 = u.gpr .rax := by
      rw [o₂ _ (by decide), e₁.gpr]
    rw [e₃.gpr, h10, hv]
    apply BitVec.eq_of_toNat_eq; simp
  · rw [e₃.mem, m₂, e₁.mem]; exact hc.frame

/-- The result and the callee-saved registers. -/
theorem result_ok {t : State} (hc : Ctx L g m₀ t) (b : Bool) (hz : t.zf = some b) :
    WP isa (.seq (.ite .e (.block [.mov32 .rax (.imm 1)]) (.block [.mov32 .rax (.imm 0)]))
      (.block (.mov .r10 (.reg .rax) :: kgRestore ++ ([.mov .rax (.reg .r10)] : List Instr)))) t
      (TailPost L g m₀ (if b then 1 else 0)) := by
  refine WP.seq (WP.ite b hz (fun hb => wp_mov32i fun u e => WP.block_nil ?_) fun hb => wp_mov32i fun u e => WP.block_nil ?_)
  · have hc' : Ctx L g m₀ u := hc.regs e.rd e.wr e.mem fun r hr => e.other r (by intro h; subst h; revert hr; decide)
    exact epi_ok hc' (v := if b then 1 else 0) (by rw [e.gpr, hb]; rfl)
  · have hc' : Ctx L g m₀ u := hc.regs e.rd e.wr e.mem fun r hr => e.other r (by intro h; subst h; revert hr; decide)
    exact epi_ok hc' (v := if b then 1 else 0) (by rw [e.gpr, hb]; rfl)

end VG.Proof.SlhDsa.X86_64.VerifyTop
