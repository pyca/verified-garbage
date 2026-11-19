module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.OpenW
import VerifiedGarbage.Proof.AesGcm.AArch64.Env
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.AesCcm.BytesAt
import VerifiedGarbage.Proof.AesGcm.AArch64.Callee
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Mul
import VerifiedGarbage.Proof.AesGcm.AArch64.Fn
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Seal
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Entry
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Open
import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.ShortSeal
public import VerifiedGarbage.Proof.AesGcm.AArch64.Open
import VerifiedGarbage.Proof.AesGcm.AArch64.Cmp
public import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.Tables
import VerifiedGarbage.Proof.Gcm.Short

/-! ### `AesGcm.AArch64.Stitch.ShortOpen`, which this module and modules that import it used -/

section

/-!
# AES-GCM on AArch64, short records: `openShort`

Untrusted: everything here is checked by Lean. `openShort` opens a record of
at most 96 bytes as `open` does (`openShort_post`), once the received tag is
at `W`: `B₂` gets the ciphertext and is hashed before `B₁` is decrypted
(`b2_layout`, `ghash_lead`, `b1_gctr`), the tag (GHASH XORed with block
`p − 1` of `B₁`, `CIPH_K(J₀)`: `b1_j0`) is compared with the received one
(`cmp_ok`), and the plaintext is copied to the text (out of place, to `dst`)
only if they are equal; out of place, `dst` is zeroed if they are not.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64.Fast

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64 VG.WriteBytes
open VG.Proof.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashFrom ghash blocks zeros padLen ofBytes inc32 ctxH ctxCiph gctr)
open VG.Proof.Gcm.AArch64.Stitch (TblOk Gh8Ok)

/-- `x24 = 1 − x10`, for `x10` a bit. -/
theorem resBit_ok {b : Nat} (hb : b ≤ 1) (s : State) (h10 : s.gpr .x10 = BitVec.ofNat 64 b) :
    WP isa (.block [imm .x24 1, .sub .x .x24 .x24 .x10]) s fun s' =>
      s'.gpr .x24 = BitVec.ofNat 64 (1 - b) ∧ Regs [.x24] s s' := by
  refine WP.of_runBlock ⟨_, by arun [], ?_⟩
  refine ⟨?_, by others_tac, rfl, rfl, rfl, rfl⟩
  simp only [gpr_write, ite_true, reduceCtorEq, ite_false, h10]
  rcases (by omega_using [hb] : b = 0 ∨ b = 1) with rfl | rfl <;> rfl

/-- `openShortG` up to the branch on the tags. -/
def openShortA (tb : List Instr) : Prog isa :=
  .seq (Impl.AesGcm.AArch64.Stitch.shortPre tb)
  (.seq Impl.AesGcm.AArch64.Stitch.textIn
  (.seq Impl.AesGcm.AArch64.Stitch.ctToB2
  (.seq Impl.AesGcm.AArch64.Stitch.aadIn
  (.seq (.block (Impl.AesGcm.AArch64.Stitch.lensB ++ Impl.AesGcm.AArch64.Stitch.shortGh ++
      Impl.AesGcm.AArch64.Stitch.shortCtr))
  (.seq (Impl.Gcm.AArch64.Stitch.byRounds Impl.AesGcm.AArch64.Stitch.shortAes)
  (.seq (.block (Impl.AesGcm.AArch64.Stitch.shortTagAt uO))
  (.seq cmp
    (.block [imm .x24 1, .sub .x .x24 .x24 .x10]))))))))

/-- The rest of `openShortG to`: the plaintext to the output if the tags are
equal (out of place, the output zeroed if not), and the result. -/
def openShortB (to : Bool) : Prog isa :=
  .seq (.ite (.zero .x .x24) (wipeG to) (Impl.AesGcm.AArch64.Stitch.plainOutG to)) (.block [mov .x0 .x24])

/-- `openShortG to` is `openShortA` then `openShortB to`. -/
theorem openShort_split (to : Bool) (tb : List Instr) :
    PEq (.seq (openShortA tb) (openShortB to)) (Impl.AesGcm.AArch64.Stitch.openShortG to tb) := by
  unfold openShortA openShortB Impl.AesGcm.AArch64.Stitch.openShortG
  refine (PEq.assoc _ _ _).trans (PEq.seq_right _ ?_)
  refine (PEq.assoc _ _ _).trans (PEq.seq_right _ ?_)
  refine (PEq.assoc _ _ _).trans (PEq.seq_right _ ?_)
  refine (PEq.assoc _ _ _).trans (PEq.seq_right _ ?_)
  refine (PEq.assoc _ _ _).trans (PEq.seq_right _ ?_)
  refine (PEq.assoc _ _ _).trans (PEq.seq_right _ ?_)
  refine (PEq.assoc _ _ _).trans (PEq.seq_right _ ?_)
  exact PEq.assoc _ _ _

/-- The received tag is the tag of the record. -/
abbrev tagEqS (Ctx Np A D Tg : Addr) (R al n tl : Nat) (s₀ : State) : Prop :=
  (Spec.Gcm.fullTag (ctxCiph s₀.mem Ctx R) (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np 12) (bytesAt s₀.mem A al)
    (bytesAt s₀.mem D n)).take tl = bytesAt s₀.mem Tg tl

/-- What `openShortA` leaves: the result bit in `x24`, the plaintext in `B₁`,
the text as it was, and the output at `O` (in place the text), its length
still at `W + lenO`. -/
structure ShortMid (Wn : Nat) (to : Bool) (Ctx W SP Np A D O Tg : Addr) (R al n tl : Nat) (s₀ u : State) : Prop where
  env : Env Wn Ctx (W + BitVec.ofNat 64 16) W SP u
  sv : SavedAt u.mem W s₀
  rd : u.rd = s₀.rd
  wr : u.wr = s₀.wr
  x24 : u.gpr .x24 = BitVec.ofNat 64 (1 - if tagEqS Ctx Np A D Tg R al n tl s₀ then 0 else 1)
  x25 : u.gpr .x25 = BitVec.ofNat 64 (16 * ((n + 15) / 16))
  x26 : u.gpr .x26 = BitVec.ofNat 64 n
  x27 : u.gpr .x27 = D
  pt : bytesAt u.mem (W + BitVec.ofNat 64 (880 - 16 * ((n + 15) / 16))) n =
    gctr (ctxCiph s₀.mem Ctx R) (inc32 (Spec.Gcm.j0 (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np 12))) (bytesAt s₀.mem D n)
  dat : bytesAt u.mem D n = bytesAt s₀.mem D n
  out : cond to (OutIn Ctx W D O n u) (O = D)
  ow : DataW Ctx (W + BitVec.ofNat 64 16) W u O n
  sN : u.mem.readW (W + BitVec.ofNat 64 240) 64 = BitVec.ofNat 64 n

/-- `openShortA`, from the state `open` leaves once the received tag is at
`W`, for a record of at most 96 bytes. -/
theorem openShortA_ok {Wn : Nat} (gh : Gh8Ok) {tb : List Instr} {to : Bool} {Ctx W SP Np A D O Tg : Addr} {R al n tl : Nat}
    {s₀ t : State} (o : OpenInG Wn to Ctx W SP Np A D O Tg R 12 al n tl s₀ t)
    (h4 : t.gpr .x4 = A) (h5 : t.gpr .x5 = BitVec.ofNat 64 al) (h6 : t.gpr .x6 = D)
    (h7 : t.gpr .x7 = BitVec.ofNat 64 n) (h16 : al ≤ 16) (hhi : n ≤ 96)
    (hT : bytesAt t.mem W tl = bytesAt s₀.mem Tg tl) (hok : Spec.Gcm.tagLenOk tl = true)
    (htb : ∀ u : State, Env Wn Ctx (W + BitVec.ofNat 64 16) W SP u → u.rd = s₀.rd → u.wr = s₀.wr →
      Frame [workR Wn W, ⟨O, n⟩] s₀.mem u.mem → WP isa (.block tb) u (Stitch.TblPost W (ctxH s₀.mem Ctx) u)) :
    WP isa (openShortA tb) t (ShortMid Wn to Ctx W SP Np A D O Tg R al n tl s₀) := by
  have L := o.lay
  have he₁ := o.env
  have hRb := o.rounds
  have perm := he₁.perm
  have ddW := o.ddW
  have daW := o.daW
  have dcW := o.dcW
  obtain ⟨hc₀, hH₀, hN₀, hA₀, hD₀⟩ := o.vals
  obtain hdk := dataOk_of o.dat
  have hnlt : n < 2 ^ 64 := hdk.lt
  obtain htl : tl ≤ 16 := by simp [Spec.Gcm.tagLenOk] at hok; omega_arith
  obtain sub16 : Region.Sub ⟨W + BitVec.ofNat 64 16, 80⟩ (workR Wn W) := Lay.wSub (by decide)
  obtain hJ : J0In Wn Ctx (W + BitVec.ofNat 64 16) W SP t.gpr (ctxH s₀.mem Ctx) Np 12 t :=
    ⟨he₁, fun _ _ => rfl, o.x23, o.x24, o.x26, o.x27, o.non, hH₀⟩
  generalize hc : (n + 15) / 16 = c
  obtain hc6 : c ≤ 6 := by omega_arith
  obtain hcn : n ≤ 16 * c := by omega_arith
  obtain hcn' : 16 * c ≤ n + 15 := by omega_arith
  unfold openShortA Impl.AesGcm.AArch64.Stitch.shortPre
  -- `J₀`, the first counter block, and the lengths.
  refine WP.seq (WP.seq (WP.block_append_iff.mpr (WP.block_append_iff.mpr
    (WP.mono (WP.with_rdwr (WP.block_and (j012_ok L hJ) (j012_others hJ))) fun s₂ ⟨⟨h₂, o₂⟩, rd₂, wr₂⟩ =>
      WP.mono (WP.with_rdwr (WP.block_and (initState_ok L h₂) (initState_others h₂.env)))
        fun s₃ ⟨⟨h₃, o₃⟩, rd₃, wr₃⟩ => ?_))))
  rw [hN₀] at h₃
  obtain o₁₃ : ∀ r ∉ [Reg.x9, .x10, .x11, .x12], s₃.gpr r = t.gpr r := fun r hr => by rw [o₃ r hr, o₂ r hr]
  obtain F₃ : Frame [workR Wn W, ⟨O, n⟩] s₀.mem s₃.mem := by
    obtain wE : ∀ {r : Region}, Region.Sub r (workR Wn W) → ∃ r' ∈ [workR Wn W, (⟨O, n⟩ : Region)], Region.Sub r r' :=
      fun h => ⟨_, List.mem_cons_self .., h⟩
    obtain j0W : ∀ r ∈ j0Frame (W + BitVec.ofNat 64 16) W, Region.Sub r (workR Wn W) := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact sub16
      · exact Lay.wSub (by decide)
      · exact Lay.wSub (by decide)
    exact (o.fr.sub fun r hr => wE (entryFr_work to W r hr)).trans (h₃.frame.sub fun r hr => wE (j0W r hr))
  refine WP.mono (Stitch.shortLen_ok (n := n) (D := D) (al := al) s₃ (by rw [o₁₃ _ (by decide), h7])
    (by rw [o₁₃ _ (by decide), h6]) (by rw [o₁₃ _ (by decide), h5]) (by omega_arith))
    fun t₀ ⟨x26₅, x27₅, x24₅, x25₅, g₅, m₅, v₅, sp₅, rd₅, wr₅⟩ => ?_
  rw [hc] at x25₅
  obtain he₅ : Env Wn Ctx (W + BitVec.ofNat 64 16) W SP t₀ := h₃.env.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact g₅ _ (by decide) (by decide) (by decide) (by decide)) sp₅ rd₅ wr₅
  -- The table.
  refine WP.seq (WP.mono (htb t₀ he₅ (by rw [rd₅, rd₃, rd₂, o.rd₀]) (by rw [wr₅, wr₃, wr₂, o.wr₀])
    (by rw [m₅]; exact F₃)) fun s₄ ⟨tbl₄, ft₄, g₄, sp₄, rd₄, wr₄⟩ => ?_)
  rw [m₅] at ft₄
  obtain he₄ : Env Wn Ctx (W + BitVec.ofNat 64 16) W SP s₄ := he₅.keep (fun r hr => g₄ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide)) sp₄ rd₄ wr₄
  -- The buffers zeroed.
  refine WP.mono (Stitch.zeroBufs_ok (c := c) hc6 s₄ he₄.x19 (by rw [g₄ _ (by decide), x25₅])
    he₄.perm.w) fun s₆ ⟨m₆, g₆, sp₆, rd₆, wr₆⟩ => ?_
  obtain he₆ : Env Wn Ctx (W + BitVec.ofNat 64 16) W SP s₆ := he₄.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact g₆ _ (by decide)) sp₆ rd₆ wr₆
  -- What `shortLen` and the entry leave, kept since.
  obtain k₆ : ∀ r ∉ [Reg.x5, .x9, .x10, .x11, .x12, .x24, .x25, .x26, .x27], s₆.gpr r = t.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g₆ _ hr.2.1, g₄ _ hr.1, g₅ _ hr.2.2.2.2.2.1 hr.2.2.2.2.2.2.1 hr.2.2.2.2.2.2.2.1 hr.2.2.2.2.2.2.2.2,
      o₁₃ _ (by simp [hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1])]
  obtain x25₆ : s₆.gpr .x25 = BitVec.ofNat 64 (16 * c) := by rw [g₆ _ (by decide), g₄ _ (by decide), x25₅]
  obtain x26₆ : s₆.gpr .x26 = BitVec.ofNat 64 n := by rw [g₆ _ (by decide), g₄ _ (by decide), x26₅]
  obtain x27₆ : s₆.gpr .x27 = D := by rw [g₆ _ (by decide), g₄ _ (by decide), x27₅]
  obtain x24₆ : s₆.gpr .x24 = BitVec.ofNat 64 al := by rw [g₆ _ (by decide), g₄ _ (by decide), x24₅]
  obtain x4₆ : s₆.gpr .x4 = A := by rw [k₆ _ (by decide), h4]
  obtain rd₆' : s₆.rd = s₀.rd := by rw [rd₆, rd₄, rd₅, rd₃, rd₂, o.rd₀]
  obtain wr₆' : s₆.wr = s₀.wr := by rw [wr₆, wr₄, wr₅, wr₃, wr₂, o.wr₀]
  obtain x22₆ : s₆.gpr .x22 = BitVec.ofNat 64 R := by rw [k₆ _ (by decide), o.x22]
  obtain x28₆ : s₆.gpr .x28 = BitVec.ofNat 64 tl := by rw [k₆ _ (by decide), o.x28]
  obtain hw : ∀ {u : State}, u.wr = s₀.wr → Covers [⟨W, Wn⟩] u.wr := fun h => by rw [h, ← o.wr₀]; exact perm.w
  -- The ciphertext, to block `p` of `B₁`.
  unfold Impl.AesGcm.AArch64.Stitch.textIn
  refine WP.seq (WP.seq ?_)
  rw [WP.block_append_iff]
  obtain ⟨t₁, run₁, x11₁, g₁', m₁', _, sp₁', rd₁', wr₁'⟩ := Stitch.atP_ok (c := c) .x11
    Impl.AesGcm.AArch64.Stitch.b1O 1 (by decide) (by unfold Impl.AesGcm.AArch64.Stitch.b1O; omega_arith) s₆ he₆.x19
    x25₆ (by decide)
  refine WP.of_runBlock ⟨t₁, run₁, ?_⟩
  obtain ⟨s₇, run₇, x12₇, x13₇, r₇⟩ : ∃ s₇, runBlock isa [mov .x12 .x27, mov .x13 .x26] t₁ = some s₇ ∧
      s₇.gpr .x12 = D ∧ s₇.gpr .x13 = BitVec.ofNat 64 n ∧ Regs [.x12, .x13] t₁ s₇ := by
    refine ⟨_, by arun [], ?_⟩
    exact ⟨by simp [gpr_write, g₁' .x27 (by decide), x27₆], by simp [gpr_write, g₁' .x26 (by decide), x26₆],
      ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
  refine WP.of_runBlock ⟨s₇, run₇, ?_⟩
  obtain x11₇ : s₇.gpr .x11 = W + BitVec.ofNat 64 (880 - 16 * c) := by
    rw [r₇.others _ (by decide), x11₁]; rfl
  obtain rd₇ : s₇.rd = s₀.rd := by rw [r₇.rd, rd₁', rd₆']
  obtain wr₇ : s₇.wr = s₀.wr := by rw [r₇.wr, wr₁', wr₆']
  obtain m₇ : s₇.mem = s₆.mem := by rw [r₇.mem, m₁']
  refine WP.mono (Stitch.copyQ_ok s₇ ⟨x12₇, x11₇, x13₇, by omega_arith,
    by rw [rd₇, wr₇, ← o.rd₀, ← o.wr₀]; exact hdk.1,
    by rw [wr₇]; exact covers_off (hw rfl) (by omega_arith) (by decide), ddW.sub_right (Lay.wSub (by omega_arith))⟩)
    fun s₈ ⟨m₈, g₈, sp₈, rd₈, wr₈⟩ => ?_
  -- The registers kept since `zeroBufs`.
  obtain kk : ∀ {u v : State} {rs : List Reg}, (∀ r, r ∉ rs → v.gpr r = u.gpr r) →
      (∀ r ∈ [Reg.x4, .x19, .x20, .x21, .x22, .x24, .x25, .x26, .x27, .x28], r ∉ rs) →
      (∀ r ∈ [Reg.x4, .x19, .x20, .x21, .x22, .x24, .x25, .x26, .x27, .x28], u.gpr r = s₆.gpr r) →
      ∀ r ∈ [Reg.x4, .x19, .x20, .x21, .x22, .x24, .x25, .x26, .x27, .x28], v.gpr r = s₆.gpr r :=
    fun hg hd hu r hr => by rw [hg r (hd r hr), hu r hr]
  obtain k₈ : ∀ r ∈ [Reg.x4, .x19, .x20, .x21, .x22, .x24, .x25, .x26, .x27, .x28], s₈.gpr r = s₆.gpr r :=
    kk g₈ (by decide) (kk r₇.others (by decide) (kk (rs := [.x11]) (fun r h => g₁' r (by simpa using h))
      (by decide) fun _ _ => rfl))
  obtain he₈ : Env Wn Ctx (W + BitVec.ofNat 64 16) W SP s₈ := he₆.keep (fun r hr => k₈ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp))
    (by rw [sp₈, r₇.sp, sp₁']) (by rw [rd₈, r₇.rd, rd₁']) (by rw [wr₈, r₇.wr, wr₁'])
  -- The ciphertext, to `B₂`.
  refine WP.seq (WP.mono (Stitch.ctToB2_ok' hc6 hcn s₈ he₈.x19 (by rw [k₈ .x25 (by simp), x25₆])
    (by rw [k₈ .x26 (by simp), x26₆]) he₈.perm.w) fun s₉ ⟨m₉, g₉, sp₉, rd₉, wr₉⟩ => ?_)
  obtain k₉ := kk g₉ (by decide) k₈
  obtain he₉ : Env Wn Ctx (W + BitVec.ofNat 64 16) W SP s₉ := he₈.keep (fun r hr => g₉ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide)) sp₉ rd₉ wr₉
  obtain rd₉' : s₉.rd = s₀.rd := by rw [rd₉, rd₈, rd₇]
  obtain wr₉' : s₉.wr = s₀.wr := by rw [wr₉, wr₈, wr₇]
  -- The additional data, to `B₂`.
  refine WP.seq (WP.mono (Stitch.aadIn_ok (A := A) (al := al) hc6 s₉ he₉.x19
    (by rw [k₉ .x25 (by simp), x25₆]) he₉.perm.w (by rw [k₉ .x4 (by simp), x4₆])
    (by rw [k₉ .x24 (by simp), x24₆]) h16
    (by rw [rd₉', wr₉', ← o.rd₀, ← o.wr₀]; exact o.aad.1) (daW.sub_right (Lay.wSub (by omega_arith))))
    fun s₁₀ ⟨m₁₀, g₁₀, sp₁₀, rd₁₀, wr₁₀⟩ => ?_)
  obtain k₁₀ := kk g₁₀ (by decide) k₉
  obtain he₁₀ : Env Wn Ctx (W + BitVec.ofNat 64 16) W SP s₁₀ := he₉.keep (fun r hr => g₁₀ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide)) sp₁₀ rd₁₀ wr₁₀
  -- The lengths block and GHASH.
  simp only [List.append_assoc]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (Stitch.lensB_ok (al := al) (n := n) s₁₀ he₁₀.x19 he₁₀.perm.w (by rw [k₁₀ .x24 (by simp), x24₆])
    (by rw [k₁₀ .x26 (by simp), x26₆]) (by omega_arith) hnlt) fun s₁₁ ⟨lens₁₁, fL₁₁, og₁₁, sp₁₁, rd₁₁, wr₁₁, _⟩ => ?_
  obtain k₁₁ := kk (rs := [.x9, .x10]) og₁₁ (by decide) k₁₀
  obtain he₁₁ : Env Wn Ctx (W + BitVec.ofNat 64 16) W SP s₁₁ := he₁₀.keep (fun r hr => og₁₁ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide)) sp₁₁ rd₁₁ wr₁₁
  -- What the writes since the table keep.
  let BR : Region := ⟨W + BitVec.ofNat 64 768, 256⟩
  obtain one : ∀ {m m' : Mem} {q : Addr} {k : Nat}, Frame [⟨q, k⟩] m m' → Region.Sub ⟨q, k⟩ BR → Frame [BR] m m' :=
    fun h hs => h.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, hs⟩
  obtain sB : ∀ {e k : Nat}, 768 ≤ e → e + k ≤ 1024 → Region.Sub ⟨W + BitVec.ofNat 64 e, k⟩ BR :=
    fun h₁ h₂ => Offset.sub W h₁ (by omega_arith)
  have lb := Proof.AesCcm.length_bytesAt
  obtain F₄₁₁ : Frame [BR] s₄.mem s₁₁.mem := by
    obtain a₁ : Frame [BR] s₄.mem s₆.mem := by
      rw [m₆]
      exact (one (writeBytes_frame' _ List.length_replicate) (sB (by decide) (by decide))).trans
        (one (writeBytes_frame' _ List.length_replicate) (sB (by omega_arith) (by omega_arith)))
    obtain a₂ : Frame [BR] s₆.mem s₈.mem := by
      rw [m₈, m₇]; exact one (writeBytes_frame' _ (lb _ _ _)) (sB (by omega_arith) (by omega_arith))
    obtain a₃ : Frame [BR] s₈.mem s₉.mem := by
      rw [m₉]
      exact (one (writeBytes_frame' _ (lb _ _ _)) (sB (by omega_arith) (by omega_arith))).trans
        (one (writeBytes_frame' _ List.length_replicate) (sB (by omega_arith) (by omega_arith)))
    obtain a₄ : Frame [BR] s₉.mem s₁₀.mem := by
      rw [m₁₀]; exact one (writeBytes_frame' _ (lb _ _ _)) (sB (by omega_arith) (by omega_arith))
    exact (((a₁.trans a₂).trans a₃).trans a₄).trans (one fL₁₁ (sB (by decide) (by decide)))
  obtain one1 : ∀ {X r : Region}, X.Disjoint r → ∀ r' ∈ [r], X.Disjoint r' := fun h r' hr' => by
    simp only [List.mem_singleton] at hr'; subst hr'; exact h
  obtain dWW : ∀ {d k e j : Nat}, d + k ≤ e ∨ e + j ≤ d → d + k ≤ Wn → e + j ≤ Wn →
      (⟨W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 e, j⟩ :=
    fun h h₁ h₂ => Offset.disjoint W h (by omega_arith) (by omega_arith)
  obtain tbl₁₁ : TblOk s₁₁.mem W (ctxH s₀.mem Ctx) :=
    tblOk_frame tbl₄ F₄₁₁ (one1 (dWW (.inl (by decide)) (by decide) (by decide)))
  rw [WP.block_append_iff]
  refine WP.mono (Stitch.shortGh_ok gh s₁₁ he₁₁.x19 tbl₁₁ (covers_left he₁₁.perm.w))
    fun s₁₂ ⟨y₁₂, g₁₂, m₁₂, sp₁₂, rd₁₂, wr₁₂⟩ => ?_
  obtain k₁₂ := kk (rs := [.x9, .x12]) (fun r h => g₁₂ r (fun e => h (by simp [e])) (fun e => h (by simp [e])))
    (by decide) k₁₁
  obtain he₁₂ : Env Wn Ctx (W + BitVec.ofNat 64 16) W SP s₁₂ := he₁₁.keep (fun r hr => k₁₂ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp) |>.trans (k₁₁ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp)).symm) sp₁₂ rd₁₂ wr₁₂
  -- The counter, and one pass of AES over `B₁`.
  refine WP.mono (Stitch.shortCtr_ok (W := W) (St := W + BitVec.ofNat 64 16) hc6 s₁₂ he₁₂.x19 he₁₂.x20
    (by rw [k₁₂ .x25 (by simp), x25₆]) (he₁₂.perm.stR (by decide)))
    fun s₁₃ ⟨x10₁₃, x9₁₃, g₁₃, m₁₃, v₁₃, sp₁₃, rd₁₃, wr₁₃⟩ => ?_
  obtain k₁₃ := kk (rs := [.x9, .x10]) (fun r h => g₁₃ r (fun e => h (by simp [e])) (fun e => h (by simp [e])))
    (by decide) k₁₂
  obtain he₁₃ : Env Wn Ctx (W + BitVec.ofNat 64 16) W SP s₁₃ := he₁₂.keep (fun r hr => g₁₃ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide)) sp₁₃ rd₁₃ wr₁₃
  obtain hp₁₃ : Proof.Gcm.AArch64.Stitch.APre R 0 (2 ^ 32 + c - 7) s₁₃ := {
    rounds := hRb
    o_le := by decide
    keys := fun r hr => by
      rw [Proof.Gcm.AArch64.Stitch.kp, he₁₃.x21]
      exact in_off he₁₃.perm.ctx (by omega_arith) (by decide)
    ctr := by
      rw [Proof.Gcm.AArch64.Stitch.cbA, he₁₃.x20, add_ofNat_zero]
      exact he₁₃.perm.stR (by decide)
    data := fun j hj => by
      rw [x9₁₃, Offset.add_add]
      exact he₁₃.perm.wR (by unfold Impl.AesGcm.AArch64.Stitch.b1O; omega_arith)
    x10 := by
      rw [x10₁₃]
      simp only [Proof.Gcm.AArch64.Stitch.c0, Proof.Gcm.AArch64.Stitch.cbk, Proof.Gcm.AArch64.Stitch.cbA, m₁₃,
        he₁₃.x20] }
  refine WP.seq (WP.mono (Stitch.shortAesB_ok s₁₃ hp₁₃ (by rw [k₁₃ .x22 (by simp), x22₆]) x9₁₃
    (covers_off he₁₃.perm.w (by decide) (by decide))) fun s₁₄ ⟨ks₁₄, f₁₄, g₁₄, sp₁₄, rd₁₄, wr₁₄, y₁₄⟩ => ?_)
  obtain k₁₄ := kk g₁₄ (by decide) k₁₃
  obtain he₁₄ : Env Wn Ctx (W + BitVec.ofNat 64 16) W SP s₁₄ := he₁₃.keep (fun r hr => g₁₄ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide)) sp₁₄ rd₁₄ wr₁₄
  -- The tag, at `W + uO`.
  refine WP.seq (WP.mono (Stitch.shortTagAt_ok (W := W) (o := 112)
    (g := Spec.Gcm.ghashFrom (ctxH s₀.mem Ctx) 0 ((List.range 8).map fun j =>
      Spec.Gcm.blockAt s₁₁.mem (W + BitVec.ofNat 64 (Impl.AesGcm.AArch64.Stitch.b2O + 16 * j))))
    (.inr rfl) hc6 s₁₄ he₁₄.x19
    (by rw [k₁₄ .x25 (by simp), x25₆]) (by rw [y₁₄, v₁₃]; exact y₁₂) he₁₄.perm.w)
    fun s₁₅ ⟨tag₁₅, fT₁₅, g₁₅, sp₁₅, rd₁₅, wr₁₅⟩ => ?_)
  obtain k₁₅ := kk (rs := [.x9]) (fun r h => g₁₅ r (fun e => h (by simp [e]))) (by decide) k₁₄
  obtain he₁₅ : Env Wn Ctx (W + BitVec.ofNat 64 16) W SP s₁₅ := he₁₄.keep (fun r hr => g₁₅ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide)) sp₁₅ rd₁₅ wr₁₅
  -- The tags compared.
  refine WP.seq (WP.mono (WP.with_rdwr (WP.gprs (rs := [.x25, .x26, .x27]) (cmp_ok L (k := s₁₅.gpr) he₁₅
      (fun _ _ => rfl) (by rw [k₁₅ .x28 (by simp), x28₆]) htl) (by decide) (by decide)))
    fun s₁₆ ⟨⟨⟨x10₁₆, he₁₆, _, _, fC₁₆⟩, gk₁₆⟩, rd₁₆, wr₁₆⟩ => ?_)
  -- The bytes, through the writes.
  obtain selfB : ∀ (m : Mem) (q : Addr) (xs : List Byte) {k : Nat}, xs.length = k → k < 2 ^ 64 →
      bytesAt (writeBytes m q xs) q k = xs := fun m q xs _ hk hk' => by
    subst hk; exact bytesAt_writeBytes_self m q xs hk'
  obtain wf : ∀ (m : Mem) (q : Addr) (xs : List Byte) {k : Nat}, xs.length = k →
      Frame [⟨q, k⟩] m (writeBytes m q xs) := fun m _ _ _ hk => writeBytes_frame' m hk
  obtain dDW : ∀ {e j : Nat}, e + j ≤ Wn → (⟨D, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 e, j⟩ :=
    fun h => ddW.sub_right (Lay.wSub h)
  obtain oneW : ∀ {m m' : Mem} {rs : List Region}, Frame rs m m' → (∀ r ∈ rs, Region.Sub r (workR Wn W)) →
      Frame [workR Wn W] m m' := fun h hs => h.sub fun r hr => ⟨_, List.mem_singleton_self _, hs r hr⟩
  obtain sW1 : ∀ {e k : Nat}, e + k ≤ Wn → ∀ r ∈ [(⟨W + BitVec.ofNat 64 e, k⟩ : Region)], Region.Sub r (workR Wn W) :=
    fun h r hr => by simp only [List.mem_singleton] at hr; subst hr; exact Lay.wSub h
  obtain Ft₄ : Frame [workR Wn W] t.mem s₄.mem := by
    refine (oneW h₃.frame fun r hr => ?_).trans (oneW ft₄ (sW1 (by decide)))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact sub16
    · exact Lay.wSub (by decide)
    · exact Lay.wSub (by decide)
  obtain Ft₁₁ : Frame [workR Wn W] t.mem s₁₁.mem := Ft₄.trans (oneW F₄₁₁ (sW1 (by decide)))
  obtain F₁₁₁₇ : Frame [workR Wn W] s₁₁.mem s₁₆.mem := by
    rw [← m₁₂, ← m₁₃]
    exact ((oneW f₁₄ (sW1 (by decide))).trans (oneW fT₁₅ (sW1 (by decide)))).trans (oneW fC₁₆ (sW1 (by decide)))
  -- The text, unchanged so far.
  obtain hDt : bytesAt s₁₆.mem D n = bytesAt s₀.mem D n := by
    rw [bytesAt_frame (Ft₁₁.trans F₁₁₁₇) (one1 ddW) (by omega_arith), hD₀]
  -- The key schedule and the counter block.
  obtain hsch : Proof.Gcm.AArch64.Stitch.sch R s₁₃ = bytesAt t.mem Ctx (16 * (R + 1)) := by
    obtain dC : (⟨Ctx, 16 * (R + 1)⟩ : Region).Disjoint (workR Wn W) := dcW.sub_left (Region.sub_prefix (by omega_arith))
    simp only [Proof.Gcm.AArch64.Stitch.sch, Proof.Gcm.AArch64.Stitch.kp, he₁₃.x21, m₁₃, m₁₂]
    rw [bytesAt_frame Ft₁₁ (one1 dC) (by omega_arith)]
  obtain hciph : Spec.Gcm.aesWith R (Proof.Gcm.AArch64.Stitch.sch R s₁₃) = ctxCiph s₀.mem Ctx R := by
    rw [hsch]; exact hc₀
  generalize hJ0 : Spec.Gcm.j0 (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np 12) = J
  have cb₃ := h₃.cb
  rw [hJ0] at cb₃
  simp only [Offset.add_add] at cb₃
  obtain hcb : Proof.Gcm.AArch64.Stitch.cbk s₁₃ = inc32 J := by
    simp only [Proof.Gcm.AArch64.Stitch.cbk, Proof.Gcm.AArch64.Stitch.cbA, he₁₃.x20, Offset.add_add, m₁₃, m₁₂]
    rw [blockAt_frame F₄₁₁ (one1 (dWW (.inl (by decide)) (by decide) (by decide))),
      blockAt_frame ft₄ (one1 (dWW (.inl (by decide)) (by decide) (by decide))), cb₃]
  -- `B₁` before the pass: the ciphertext at block `p`, zeros at block `p − 1`.
  simp only [Impl.AesGcm.AArch64.Stitch.b2O, Impl.AesGcm.AArch64.Stitch.b1O] at m₆ ks₁₄ y₁₂ f₁₄ tag₁₅
  obtain B₁₁ : ∀ {e k : Nat}, 768 ≤ e → e + k ≤ 896 →
      bytesAt s₁₃.mem (W + BitVec.ofNat 64 e) k = bytesAt s₈.mem (W + BitVec.ofNat 64 e) k := fun h₁ h₂ => by
    rw [m₁₃, m₁₂, bytesAt_frame fL₁₁ (one1 (dWW (.inl (by omega_arith)) (by omega_arith) (by decide))) (by omega_arith), m₁₀,
      bytesAt_frame (wf _ _ _ (lb _ _ _)) (one1 (dWW (.inl (by omega_arith)) (by omega_arith) (by omega_arith))) (by omega_arith), m₉,
      bytesAt_frame (wf _ _ _ List.length_replicate) (one1 (dWW (.inl (by omega_arith)) (by omega_arith) (by omega_arith))) (by omega_arith),
      bytesAt_frame (wf _ _ _ (lb _ _ _)) (one1 (dWW (.inl (by omega_arith)) (by omega_arith) (by omega_arith))) (by omega_arith)]
  obtain hP : bytesAt s₁₃.mem (W + BitVec.ofNat 64 768 + BitVec.ofNat 64 (16 * (7 - c))) n = bytesAt s₀.mem D n := by
    rw [Offset.add_add, show 768 + 16 * (7 - c) = 880 - 16 * c by omega_arith, B₁₁ (by omega_arith) (by omega_arith), m₈,
      selfB _ _ _ (lb _ _ _) (by omega_arith), m₇, m₆,
      bytesAt_frame (wf _ _ _ List.length_replicate) (one1 (dDW (by omega_arith))) (by omega_arith),
      bytesAt_frame (wf _ _ _ List.length_replicate) (one1 (dDW (by decide))) (by omega_arith),
      bytesAt_frame Ft₄ (one1 ddW) (by omega_arith), hD₀]
  obtain hz₁₃ : bytesAt s₁₃.mem (W + BitVec.ofNat 64 768 + BitVec.ofNat 64 (16 * (6 - c))) 16 = zeros 16 := by
    rw [Offset.add_add, show 768 + 16 * (6 - c) = 864 - 16 * c by omega_arith, B₁₁ (by omega_arith) (by omega_arith), m₈,
      bytesAt_frame (wf _ _ _ (lb _ _ _)) (one1 (dWW (.inl (by omega_arith)) (by omega_arith) (by omega_arith))) (by decide), m₇, m₆,
      selfB _ _ _ List.length_replicate (by decide)]
    rfl
  -- After the pass: the plaintext, and `CIPH_K(J₀)`.
  rw [hcb] at ks₁₄
  obtain hPt : bytesAt s₁₄.mem (W + BitVec.ofNat 64 (880 - 16 * c)) n =
      gctr (ctxCiph s₀.mem Ctx R) (inc32 J) (bytesAt s₀.mem D n) := by
    have := Stitch.b1_gctr hcn hc6 ks₁₄ hP
    rw [Offset.add_add, show 768 + 16 * (7 - c) = 880 - 16 * c by omega_arith, hciph] at this
    exact this
  obtain hE : blockAt s₁₄.mem (W + BitVec.ofNat 64 (864 - 16 * c)) = ctxCiph s₀.mem Ctx R J := by
    have := Stitch.b1_j0 hc6 ks₁₄ hz₁₃
    rw [Offset.add_add, show 768 + 16 * (6 - c) = 864 - 16 * c by omega_arith, hciph] at this
    exact this
  -- What `B₂` holds, and its GHASH.
  obtain hZ₆ : bytesAt s₆.mem (W + BitVec.ofNat 64 896) 128 = zeros 128 := by
    rw [m₆, bytesAt_frame (wf _ _ _ List.length_replicate) (one1 (dWW (.inr (by omega_arith)) (by decide) (by omega_arith)))
      (by decide), selfB _ _ _ List.length_replicate (by decide)]
    rfl
  obtain hA₉ : bytesAt s₉.mem A al = bytesAt s₀.mem A al := by
    obtain dA : ∀ {e j : Nat}, e + j ≤ Wn → (⟨A, al⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 e, j⟩ :=
      fun h => daW.sub_right (Lay.wSub h)
    rw [m₉, bytesAt_frame (wf _ _ _ List.length_replicate) (one1 (dA (by omega_arith))) (by omega_arith),
      bytesAt_frame (wf _ _ _ (lb _ _ _)) (one1 (dA (by omega_arith))) (by omega_arith), m₈,
      bytesAt_frame (wf _ _ _ (lb _ _ _)) (one1 (dA (by omega_arith))) (by omega_arith), m₇, m₆,
      bytesAt_frame (wf _ _ _ List.length_replicate) (one1 (dA (by omega_arith))) (by omega_arith),
      bytesAt_frame (wf _ _ _ List.length_replicate) (one1 (dA (by decide))) (by omega_arith),
      bytesAt_frame Ft₄ (one1 daW) (by omega_arith), hA₀]
  obtain fY : Frame [⟨W + BitVec.ofNat 64 (880 - 16 * c), n⟩] s₆.mem s₈.mem := by
    rw [m₈, m₇]; exact wf _ _ _ (lb _ _ _)
  obtain L2 := Stitch.b2_layout (G := W + BitVec.ofNat 64 896) (c := c) (n := n)
    (Q := bytesAt s₈.mem (W + BitVec.ofNat 64 (880 - 16 * c)) (16 * c)) (A := bytesAt s₉.mem A al)
    (lens := Proof.Gcm.lensBlock al n) (mZ := s₆.mem) (mY := s₈.mem) (mL := s₁₁.mem) hc6 hcn
    (by omega_arith) (lb _ _ _) (by rw [lb]; exact h16) hZ₆ fY
    (one1 (dWW (.inr (by omega_arith)) (by decide) (by omega_arith)))
    (by
      simp only [Offset.add_add]
      rw [show 896 + (112 - 16 * c) = 1008 - 16 * c by omega_arith, show 896 + (112 - 16 * c + n) = 1008 - 16 * c + n by omega_arith,
        show 896 + (96 - 16 * c) = 992 - 16 * c by omega_arith, ← m₉, ← m₁₀]
      exact fL₁₁)
    (by rw [Offset.add_add]; exact lens₁₁)
  obtain hC₈ : bytesAt s₈.mem (W + BitVec.ofNat 64 (880 - 16 * c)) n = bytesAt s₀.mem D n := by
    have h := hP
    rw [Offset.add_add, show 768 + 16 * (7 - c) = 880 - 16 * c by omega_arith] at h
    rw [← B₁₁ (e := 880 - 16 * c) (k := n) (by omega_arith) (by omega_arith)]; exact h
  rw [← Proof.AesCcm.bytesAt_prefix _ _ (show n ≤ 16 * c from hcn), hC₈, hA₉,
    show 16 * c - n = Spec.Gcm.padLen (bytesAt s₀.mem D n).length by rw [lb]; simp only [Spec.Gcm.padLen]; omega_arith,
    show Proof.Gcm.lensBlock al n = Proof.Gcm.lensBlock (bytesAt s₀.mem A al).length (bytesAt s₀.mem D n).length by
      rw [lb, lb]] at L2
  obtain hg : Spec.Gcm.ghashFrom (ctxH s₀.mem Ctx) 0 ((List.range 8).map fun j =>
      blockAt s₁₁.mem (W + BitVec.ofNat 64 (896 + 16 * j))) =
      Spec.Gcm.ghashFrom (ctxH s₀.mem Ctx) (ghash (ctxH s₀.mem Ctx)
        (blocks (Proof.Gcm.padded (bytesAt s₀.mem A al) (bytesAt s₀.mem D n))))
        [ofBytes (Proof.Gcm.lensBlock (bytesAt s₀.mem A al).length (bytesAt s₀.mem D n).length)] := by
    rw [show ((List.range 8).map fun j => blockAt s₁₁.mem (W + BitVec.ofNat 64 (896 + 16 * j))) =
        Spec.Gcm.blocksAt s₁₁.mem (W + BitVec.ofNat 64 896) 8 by simp only [Spec.Gcm.blocksAt, Offset.add_add],
      Proof.Gcm.blocksAt_eq, L2]
    exact Proof.Gcm.ghash_lead _ _ (by rw [lb]; exact h16)
  -- The tags.
  obtain bt : ∀ (m : Mem) (p : Addr), bytesAt m p 16 = Spec.Gcm.toBytes (blockAt m p) := fun m p => by
    rw [blockAt, Proof.Cmac.toBytes_ofBytes (lb _ _ _)]
  obtain hTc : bytesAt s₁₅.mem (W + BitVec.ofNat 64 112) tl =
      (Spec.Gcm.fullTag (ctxCiph s₀.mem Ctx R) (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np 12) (bytesAt s₀.mem A al)
        (bytesAt s₀.mem D n)).take tl := by
    rw [Proof.AesCcm.bytesAt_prefix _ _ htl, bt, tag₁₅, hE, hg, Proof.Gcm.fullTag_eq, hJ0]
  obtain hTr : bytesAt s₁₅.mem W tl = bytesAt s₀.mem Tg tl := by
    obtain dT : ∀ {e j : Nat}, 16 ≤ e → e + j ≤ Wn → (⟨W, tl⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 e, j⟩ :=
      fun h₁ h₂ => Offset.base_disjoint W (by omega_arith) (by omega_arith)
    rw [bytesAt_frame fT₁₅ (one1 (dT (by decide) (by decide))) (by omega_arith),
      bytesAt_frame f₁₄ (one1 (dT (by decide) (by decide))) (by omega_arith), m₁₃, m₁₂,
      bytesAt_frame F₄₁₁ (one1 (dT (by decide) (by decide))) (by omega_arith),
      bytesAt_frame ft₄ (one1 (dT (by decide) (by decide))) (by omega_arith),
      bytesAt_frame h₃.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> exact dT (by decide) (by decide)) (by omega_arith), hT]
  -- The result: 1 exactly when the tags are equal.
  simp only [hTc, hTr] at x10₁₆
  obtain hb1 : (if ((Spec.Gcm.fullTag (ctxCiph s₀.mem Ctx R) (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np 12) (bytesAt s₀.mem A al) (bytesAt s₀.mem D n)).take tl = bytesAt s₀.mem Tg tl) then 0 else 1) ≤ 1 := by split <;> decide
  refine WP.mono (resBit_ok hb1 s₁₆ x10₁₆) fun s₁₇ ⟨x24₁₇, r₁₇⟩ => ?_
  obtain he₁₇ : Env Wn Ctx (W + BitVec.ofNat 64 16) W SP s₁₇ := he₁₆.keep (fun r hr => r₁₇.others r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide)) r₁₇.sp r₁₇.rd r₁₇.wr
  obtain F₁₁₁₇' : Frame [workR Wn W] s₁₁.mem s₁₇.mem := by rw [r₁₇.mem]; exact F₁₁₁₇
  -- What the frames since `t` keep of the saved registers.
  obtain sv₁₇ : SavedAt s₁₇.mem W s₀ := by
    obtain h₁ := (o.sv.frame h₃.frame (saved_j0Frame L)).frame ft₄ (one1 (dWW (.inl (by decide)) (by decide) (by decide)))
    obtain h₂ := (h₁.frame F₄₁₁ (one1 (dWW (.inl (by decide)) (by decide) (by decide))))
    rw [← m₁₂, ← m₁₃] at h₂
    obtain h₃' := ((h₂.frame f₁₄ (one1 (dWW (.inl (by decide)) (by decide) (by decide)))).frame fT₁₅
      (one1 (dWW (.inr (by decide)) (by decide) (by decide)))).frame fC₁₆ (saved_cmp L)
    rw [r₁₇.mem]; exact h₃'
  obtain dB : ∀ {e j : Nat}, e + j ≤ Wn → (880 - 16 * c + n ≤ e ∨ e + j ≤ 880 - 16 * c) →
      (⟨W + BitVec.ofNat 64 (880 - 16 * c), n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 e, j⟩ :=
    fun h₁ h₂ => dWW h₂ (by omega_arith) h₁
  -- What the path writes is in `fastFrameP`, apart from the slots and `dst`'s.
  obtain Ff : Frame (fastFrameP Wn W) t.mem s₁₇.mem := by
    obtain a₀ : Frame (fastFrameP Wn W) t.mem s₃.mem := h₃.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact fastP_lo (d := 16) (k := 80) (by decide) (by decide)
      · exact fastP_lo (by decide) (by decide)
      · exact fastP_hi (.inr ⟨by decide, by decide⟩)
    obtain a₁ : Frame (fastFrameP Wn W) s₃.mem s₄.mem := ft₄.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact fastP_hi (.inr ⟨by decide, by decide⟩)
    obtain a₂ : Frame (fastFrameP Wn W) s₄.mem s₁₃.mem := by
      rw [m₁₃, m₁₂]
      exact F₄₁₁.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact fastP_hi (.inr ⟨by decide, by decide⟩)
    obtain a₃ : Frame (fastFrameP Wn W) s₁₃.mem s₁₄.mem := f₁₄.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact fastP_hi (.inr ⟨by decide, by decide⟩)
    obtain a₄ : Frame (fastFrameP Wn W) s₁₄.mem s₁₅.mem := fT₁₅.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact fastP_lo (by decide) (by decide)
    obtain a₅ : Frame (fastFrameP Wn W) s₁₅.mem s₁₆.mem := fC₁₆.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact fastP_hi (.inl ⟨by decide, by decide⟩)
    rw [r₁₇.mem]
    exact ((((a₀.trans a₁).trans a₂).trans a₃).trans a₄).trans a₅
  obtain rd₁₇' : s₁₇.rd = t.rd := by rw [r₁₇.rd, rd₁₆, rd₁₅, rd₁₄, rd₁₃, rd₁₂, rd₁₁, rd₁₀, rd₉', o.rd₀]
  obtain wr₁₇' : s₁₇.wr = t.wr := by rw [r₁₇.wr, wr₁₆, wr₁₅, wr₁₄, wr₁₃, wr₁₂, wr₁₁, wr₁₀, wr₉', o.wr₀]
  obtain sN₁₇ : s₁₇.mem.readW (W + BitVec.ofNat 64 240) 64 = BitVec.ofNat 64 n := by
    rw [slot_kept Ff (slots_fastFrameP W) (by decide) (by decide), o.sN]
  obtain out₁₇ : cond to (OutIn Ctx W D O n s₁₇) (O = D) := by
    cases to with
    | false => exact o.out
    | true =>
      exact OutIn.of_eq (o.out : OutIn Ctx W D O n t) rd₁₇' wr₁₇'
        (Ff.readW (r := ⟨W + BitVec.ofNat 64 320, 8⟩) (Region.contains_self _ _) (dst_fastFrameP W) (by decide))
  exact ⟨he₁₇, sv₁₇, by rw [r₁₇.rd, rd₁₆, rd₁₅, rd₁₄, rd₁₃, rd₁₂, rd₁₁, rd₁₀, rd₉'],
    by rw [r₁₇.wr, wr₁₆, wr₁₅, wr₁₄, wr₁₃, wr₁₂, wr₁₁, wr₁₀, wr₉'], x24₁₇,
    by rw [r₁₇.others _ (by decide), gk₁₆ .x25 (by simp), k₁₅ .x25 (by simp), x25₆, ← hc],
    by rw [r₁₇.others _ (by decide), gk₁₆ .x26 (by simp), k₁₅ .x26 (by simp), x26₆],
    by rw [r₁₇.others _ (by decide), gk₁₆ .x27 (by simp), k₁₅ .x27 (by simp), x27₆],
    by rw [hc, hJ0, r₁₇.mem, bytesAt_frame fC₁₆ (one1 (dB (by decide) (.inr (by omega_arith)))) (by omega_arith),
      bytesAt_frame fT₁₅ (one1 (dB (by decide) (.inr (by omega_arith)))) (by omega_arith), hPt],
    by rw [bytesAt_frame F₁₁₁₇' (one1 ddW) (by omega_arith), bytesAt_frame Ft₁₁ (one1 ddW) (by omega_arith), hD₀],
    out₁₇, o.outW.of_eq rd₁₇' wr₁₇', sN₁₇⟩

/-- `openShortB to`, from what `openShortA` leaves. -/
theorem openShortB_ok {Wn : Nat} {to : Bool} {Ctx W SP Np A D O Tg : Addr} {R al n tl : Nat} {s₀ t u : State}
    (o : OpenInG Wn to Ctx W SP Np A D O Tg R 12 al n tl s₀ t) (hhi : n ≤ 96) (hok : Spec.Gcm.tagLenOk tl = true)
    (m : ShortMid Wn to Ctx W SP Np A D O Tg R al n tl s₀ u) :
    WP isa (openShortB to) u (OpenPostG Wn Ctx W SP Np A O Tg R 12 al n tl (bytesAt s₀.mem D n)
      (fun m => bytesAt m O n = cond to (List.replicate n 0) (bytesAt s₀.mem D n)) s₀) := by
  obtain hnlt : n < 2 ^ 64 := (dataOk_of o.dat).lt
  have lb := Proof.AesCcm.length_bytesAt
  obtain selfB : ∀ (m : Mem) (q : Addr) (xs : List Byte) {k : Nat}, xs.length = k → k < 2 ^ 64 →
      bytesAt (writeBytes m q xs) q k = xs := fun m q xs _ hk hk' => by
    subst hk; exact bytesAt_writeBytes_self m q xs hk'
  obtain wf : ∀ (m : Mem) (q : Addr) (xs : List Byte) {k : Nat}, xs.length = k →
      Frame [⟨q, k⟩] m (writeBytes m q xs) := fun m _ _ _ hk => writeBytes_frame' m hk
  obtain one1 : ∀ {X r : Region}, X.Disjoint r → ∀ r' ∈ [r], X.Disjoint r' := fun h r' hr' => by
    simp only [List.mem_singleton] at hr'; subst hr'; exact h
  obtain ⟨he₁₇, sv₁₇, rd₁₇, wr₁₇, x24₁₇, x25₁₇, x26₁₇, x27₁₇, pt₁₇, dat₁₇, out₁₇, ow₁₇, sN₁₇⟩ := m
  have doW : (⟨O, n⟩ : Region).Disjoint ⟨W, Wn⟩ := ow₁₇.ok.w
  simp only [tagEqS] at x24₁₇
  generalize hJ0 : Spec.Gcm.j0 (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np 12) = J at pt₁₇
  generalize hc : (n + 15) / 16 = c at x25₁₇ pt₁₇
  obtain hc6 : c ≤ 6 := by omega_using [hhi, hc]
  obtain hcn : n ≤ 16 * c := by omega_using [hc]
  obtain hw : ∀ {v : State}, v.wr = s₀.wr → Covers [⟨W, Wn⟩] v.wr := fun h => by
    rw [h, ← wr₁₇]; exact he₁₇.perm.w
  unfold openShortB
  -- The end, from either branch.
  obtain fin : ∀ u : State, Env Wn Ctx (W + BitVec.ofNat 64 16) W SP u → SavedAt u.mem W s₀ →
      (((Spec.Gcm.fullTag (ctxCiph s₀.mem Ctx R) (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np 12) (bytesAt s₀.mem A al)
        (bytesAt s₀.mem D n)).take tl = bytesAt s₀.mem Tg tl) → (u.gpr .x24).setWidth 32 = 1 ∧ bytesAt u.mem O n =
        gctr (ctxCiph s₀.mem Ctx R) (inc32 J) (bytesAt s₀.mem D n)) →
      (¬((Spec.Gcm.fullTag (ctxCiph s₀.mem Ctx R) (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np 12) (bytesAt s₀.mem A al)
        (bytesAt s₀.mem D n)).take tl = bytesAt s₀.mem Tg tl) → (u.gpr .x24).setWidth 32 = 0 ∧
        bytesAt u.mem O n = cond to (List.replicate n 0) (bytesAt s₀.mem D n)) →
      WP isa (.block [mov .x0 .x24]) u (OpenPostG Wn Ctx W SP Np A O Tg R 12 al n tl (bytesAt s₀.mem D n)
        (fun m => bytesAt m O n = cond to (List.replicate n 0) (bytesAt s₀.mem D n)) s₀) := by
    intro u heu svu hy hn'
    obtain ⟨u', run', x0', r'⟩ : ∃ u', runBlock isa [mov .x0 .x24] u = some u' ∧ u'.gpr .x0 = u.gpr .x24 ∧
        Regs [.x0] u u' := by
      refine ⟨_, by arun [], ?_⟩
      exact ⟨by simp [gpr_write], ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
    refine WP.of_runBlock ⟨u', run', heu.of_regs r', by rw [r'.mem]; exact svu, ?_⟩
    rw [Spec.Gcm.openResult, ite_eq_left hok, Spec.Gcm.decryptWith]
    by_cases hc : ((Spec.Gcm.fullTag (ctxCiph s₀.mem Ctx R) (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np 12) (bytesAt s₀.mem A al) (bytesAt s₀.mem D n)).take tl = bytesAt s₀.mem Tg tl)
    · rw [ite_eq_left hc, hJ0]
      obtain ⟨a, b⟩ := hy hc
      exact ⟨by rw [x0', a], by rw [r'.mem, b]⟩
    · rw [ite_eq_right hc]
      obtain ⟨a, b⟩ := hn' hc
      exact ⟨by rw [x0', a], show bytesAt u'.mem O n = _ by rw [r'.mem, b]⟩
  refine WP.seq (WP.ite _ (eval_zero x24₁₇ (by split <;> decide)) (fun hz => ?_) (fun hz => ?_))
  · -- The tags differ: the text stays as it was, or out of place the output is zeroed.
    obtain hne : ¬((Spec.Gcm.fullTag (ctxCiph s₀.mem Ctx R) (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np 12) (bytesAt s₀.mem A al) (bytesAt s₀.mem D n)).take tl = bytesAt s₀.mem Tg tl) := fun h => by simp [h] at hz
    cases to with
    | false =>
      have e : O = D := out₁₇
      subst e
      exact WP.block_nil (fin u he₁₇ sv₁₇ (fun h => absurd h hne) fun _ => ⟨by rw [x24₁₇]; simp [hne], dat₁₇⟩)
    | true =>
      have ou : OutIn Ctx W D O n u := out₁₇
      refine WP.mono (wipeTo_ok he₁₇ ou.sO sN₁₇ ou.dw) fun s' ⟨z, f, g, sp, rd, wr⟩ => ?_
      refine fin s' (he₁₇.keep (fun r hr => g r (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl <;> decide) (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl <;> decide) (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl <;> decide)) sp rd wr)
        (sv₁₇.frame f (one1 (doW.sub_right (Lay.wSub (by decide))).symm)) (fun h => absurd h hne)
        fun _ => ⟨by rw [g _ (by decide) (by decide) (by decide), x24₁₇]; simp [hne], z⟩
  · -- The tags are equal: the plaintext to the output.
    obtain heq : ((Spec.Gcm.fullTag (ctxCiph s₀.mem Ctx R) (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np 12) (bytesAt s₀.mem A al) (bytesAt s₀.mem D n)).take tl = bytesAt s₀.mem Tg tl) := by by_contra h; simp [h] at hz
    unfold Impl.AesGcm.AArch64.Stitch.plainOutG
    refine WP.seq ?_
    rw [List.append_assoc, WP.block_append_iff]
    obtain ⟨t₂, run₂, x12t₂, g₂', m₂', _, sp₂', rd₂', wr₂'⟩ := Stitch.atP_ok (c := c) .x12
      Impl.AesGcm.AArch64.Stitch.b1O 1 (by decide) (by unfold Impl.AesGcm.AArch64.Stitch.b1O; omega_using [hc6]) u he₁₇.x19
      x25₁₇ (by decide)
    refine WP.of_runBlock ⟨t₂, run₂, ?_⟩
    obtain he₂ : Env Wn Ctx (W + BitVec.ofNat 64 16) W SP t₂ := he₁₇.keep (fun r hr => g₂' r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide)) sp₂' rd₂' wr₂'
    obtain ⟨s₁₈, run₁₈, x11₁₈, x13₁₈, r₁₈⟩ : ∃ s₁₈, runBlock isa
        (cond to ([.ldr .x .x11 .x19 dstO] : List Instr) [mov .x11 .x27] ++ [mov .x13 .x26]) t₂ = some s₁₈ ∧
        s₁₈.gpr .x11 = O ∧ s₁₈.gpr .x13 = BitVec.ofNat 64 n ∧ Regs [.x11, .x13] t₂ s₁₈ := by
      cases to with
      | false =>
        have e : O = D := out₁₇
        refine ⟨_, by arun [Bool.cond_false], ?_⟩
        exact ⟨by simp [gpr_write, g₂' .x27 (by decide), x27₁₇, e], by simp [gpr_write, g₂' .x26 (by decide), x26₁₇],
          ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
      | true =>
        have ou : OutIn Ctx W D O n u := out₁₇
        obtain q₃ := he₂.perm.wR (show 320 + 8 ≤ 512 by decide)
        obtain e₃ : t₂.mem.read (W + 320#64) 8 = O := by
          rw [show t₂.mem.read (W + 320#64) 8 = t₂.mem.readW (W + BitVec.ofNat 64 320) 64 from rfl, m₂', ou.sO]
        refine ⟨_, by arun [Bool.cond_true, he₂.x19, q₃, dstO], ?_⟩
        exact ⟨by simp [gpr_write, e₃], by simp [gpr_write, g₂' .x26 (by decide), x26₁₇],
          ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
    refine WP.of_runBlock ⟨s₁₈, run₁₈, ?_⟩
    obtain x12₁₈ : s₁₈.gpr .x12 = W + BitVec.ofNat 64 (880 - 16 * c) := by
      rw [r₁₈.others _ (by decide), x12t₂]; rfl
    obtain rd₁₈ : s₁₈.rd = s₀.rd := by
      rw [r₁₈.rd, rd₂', rd₁₇]
    obtain wr₁₈ : s₁₈.wr = s₀.wr := by
      rw [r₁₈.wr, wr₂', wr₁₇]
    refine WP.mono (Stitch.copyQ_ok s₁₈ ⟨x12₁₈, x11₁₈, x13₁₈, by omega_using [hhi],
      by rw [rd₁₈, wr₁₈]; exact covers_left (covers_off (hw rfl) (by omega_using [hhi]) (by decide)),
      by rw [r₁₈.wr, wr₂']; exact ow₁₇.wr, (doW.sub_right (Lay.wSub (by omega_using [hhi]))).symm⟩)
      fun s₁₉ ⟨m₁₉, g₁₉, sp₁₉, rd₁₉, wr₁₉⟩ => ?_
    obtain he₁₉ : Env Wn Ctx (W + BitVec.ofNat 64 16) W SP s₁₉ := he₁₇.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> rw [g₁₉ _ (by decide), r₁₈.others _ (by decide), g₂' _ (by decide)])
      (by rw [sp₁₉, r₁₈.sp, sp₂']) (by rw [rd₁₉, r₁₈.rd, rd₂']) (by rw [wr₁₉, r₁₈.wr, wr₂'])
    obtain m₁₈ : s₁₈.mem = u.mem := by rw [r₁₈.mem, m₂']
    refine fin s₁₉ he₁₉ (by
        rw [m₁₉]
        exact sv₁₇.frame (by rw [← m₁₈]; exact wf _ _ _ (lb _ _ _))
          (one1 (doW.sub_right (Lay.wSub (by decide))).symm))
      (fun _ => ⟨?_, ?_⟩) fun h => absurd heq h
    · rw [g₁₉ _ (by decide), r₁₈.others _ (by decide), g₂' _ (by decide), x24₁₇]
      simp [heq]
    · rw [m₁₉, selfB _ _ _ (lb _ _ _) (by omega_using [hhi]), m₁₈, pt₁₇]

/-- `openShortG to`, from the state `open` (or `open_to`) leaves once the
received tag is at `W`, for a record of at most 96 bytes. -/
theorem openShort_post {Wn : Nat} (gh : Gh8Ok) {tb : List Instr} {to : Bool} {Ctx W SP Np A D O Tg : Addr} {R al n tl : Nat}
    {s₀ t : State} (o : OpenInG Wn to Ctx W SP Np A D O Tg R 12 al n tl s₀ t)
    (h4 : t.gpr .x4 = A) (h5 : t.gpr .x5 = BitVec.ofNat 64 al) (h6 : t.gpr .x6 = D)
    (h7 : t.gpr .x7 = BitVec.ofNat 64 n) (h16 : al ≤ 16) (hhi : n ≤ 96)
    (hT : bytesAt t.mem W tl = bytesAt s₀.mem Tg tl) (hok : Spec.Gcm.tagLenOk tl = true)
    (htb : ∀ u : State, Env Wn Ctx (W + BitVec.ofNat 64 16) W SP u → u.rd = s₀.rd → u.wr = s₀.wr →
      Frame [workR Wn W, ⟨O, n⟩] s₀.mem u.mem → WP isa (.block tb) u (Stitch.TblPost W (ctxH s₀.mem Ctx) u)) :
    WP isa (Impl.AesGcm.AArch64.Stitch.openShortG to tb) t (OpenPostG Wn Ctx W SP Np A O Tg R 12 al n tl
      (bytesAt s₀.mem D n) (fun m => bytesAt m O n = cond to (List.replicate n 0) (bytesAt s₀.mem D n)) s₀) :=
  (openShort_split to tb).symm.wp (WP.seq (WP.mono (openShortA_ok gh o h4 h5 h6 h7 h16 hhi hT hok htb)
    fun _ m => openShortB_ok o hhi hok m))

end VG.Proof.AesGcm.AArch64.Fast

end

end

/-!
# AES-GCM on AArch64, short records: `openWithS` with the short path

Untrusted: everything here is checked by Lean. `openWithSG c to` with `sh`
takes `openShortFG` for records of 17 to `shortMax` bytes (`shortThr`,
`shortMin`), which leaves what `open` (or out of place `open_to`) must
(`openShort_post`), and otherwise the other paths (`openSelS_wp`): in place
`openWithSh_wp`, out of place `openToWithSh_wp`.
-/

@[expose] public section

namespace VG.Proof.AesGcm.AArch64.Fast

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64
open VG.Proof.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (ctxH ctxCiph)
open VG.Proof.Gcm.AArch64.Stitch (Gh8Ok)

/-- `TbForO` without the key `H'` at `W + hO`, which `pwTbl` does not read. -/
def TbForOP (Wn : Nat) (tb : List Instr) (Ctx W SP D : Addr) (n : Nat) (s₀ : State) : Prop :=
  ∀ u : State, Env Wn Ctx (W + BitVec.ofNat 64 16) W SP u → u.rd = s₀.rd → u.wr = s₀.wr →
    Frame [workR Wn W, ⟨D, n⟩] s₀.mem u.mem → WP isa (.block tb) u (Stitch.TblPost W (Spec.Gcm.ctxH s₀.mem Ctx) u)

theorem TbForOP.tbFor {Wn : Nat} {tb : List Instr} {Ctx W SP D : Addr} {n : Nat} {s₀ : State}
    (h : TbForOP Wn tb Ctx W SP D n s₀) : TbForO Wn tb Ctx W SP D n s₀ :=
  fun u he hrd hwr hf _ => h u he hrd hwr hf

/-- The branch on the tag length failing: 0 returned, and out of place the
output zeroed (in place, the text as it was). -/
theorem failG_ok {Wn : Nat} {to : Bool} {Ctx W SP Np A D O Tg : Addr} {R nl al n tl : Nat} {s₀ s₃ : State}
    (o : OpenInG Wn to Ctx W SP Np A D O Tg R nl al n tl s₀ s₃) (hok : Spec.Gcm.tagLenOk tl = false) :
    WP isa (.seq (.block [imm .x0 0]) (wipeG to)) s₃ (OpenPostG Wn Ctx W SP Np A O Tg R nl al n tl
      (bytesAt s₀.mem D n) (fun m => bytesAt m O n = cond to (List.replicate n 0) (bytesAt s₀.mem D n)) s₀) := by
  cases to with
  | true => exact failTo_ok o hok
  | false =>
    have e : O = D := o.out
    subst e
    exact WP.seq (WP.mono (failZero_ok (C := bytesAt s₀.mem O n) (F := fun m => bytesAt m O n = bytesAt s₀.mem O n)
      o o.vals.2.2.2.2 hok) fun u q => WP.block_nil q)

/-- `openWithSG c to w tb cl sh` after its entry. -/
def openSelS (c : Callees) (to : Bool) (tb : List Instr) (cl : Prog isa) (sh : Bool) : Prog isa :=
  .seq Impl.AesGcm.AArch64.Fast.cond (.ite (.zero .x .x10)
      (if sh then
        .seq (.block Impl.AesGcm.AArch64.Stitch.shortThr) (.ite (.zero .x .x9)
          (.seq (.block Impl.AesGcm.AArch64.Stitch.shortMin) (.ite (.zero .x .x9)
            (Impl.AesGcm.AArch64.Fast.openFastPG c to cl) (Impl.AesGcm.AArch64.Stitch.openShortFG to tb)))
          (.seq (.block Impl.AesGcm.AArch64.Stitch.thr) (.ite (.zero .x .x9)
            (Impl.AesGcm.AArch64.Fast.openFastPG c to cl) (Impl.AesGcm.AArch64.Stitch.openFastSG c to tb cl))))
      else .seq (.block Impl.AesGcm.AArch64.Stitch.thr) (.ite (.zero .x .x9)
        (Impl.AesGcm.AArch64.Fast.openFastPG c to cl) (Impl.AesGcm.AArch64.Stitch.openFastSG c to tb cl)))
      (openRestG c to))

theorem openWithSG_eq (c : Callees) (to : Bool) (w : Nat) (tb : List Instr) (cl : Prog isa) (sh : Bool) :
    Impl.AesGcm.AArch64.Stitch.openWithSG c to w tb cl sh = .seq (.block (openEntryG to w)) (openSelS c to tb cl sh) :=
  rfl

/-- What `openWithSG c to` leaves, from `s`, of the text at `x6` and the
output at `O`: the plaintext there if the tag is right, and otherwise the
text as it was in place, zeros out of place. -/
abbrev OpenSPost (to : Bool) (O Tg : Addr) (tl : Nat) (s s' : State) : Prop :=
  GprAbi s s' ∧
    match Spec.Gcm.openResult (ctxCiph s.mem (s.gpr .x0) (s.gpr .x1).toNat) (ctxH s.mem (s.gpr .x0)) tl
        (bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) (bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat)
        (bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat) (bytesAt s.mem Tg tl) with
    | some pt => (s'.gpr .x0).setWidth 32 = 1 ∧ bytesAt s'.mem O (s.gpr .x7).toNat = pt
    | none => (s'.gpr .x0).setWidth 32 = 0 ∧
        bytesAt s'.mem O (s.gpr .x7).toNat = cond to (List.replicate (s.gpr .x7).toNat 0)
          (bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat)

/-- `openSelS`, after the entry of `open` or `open_to` (`to`) from `s`, with
the text at `x6` and the output at `O`, for a `tb` that writes the table
without `H'` (`TbForOP`) and a `cl` that hashes as `vg_ghash` when run with
memory changed since the entry only in the working space and the output. -/
theorem openSelS_wp {Wn : Nat} (v : GcmImpl) (cl : Prog isa) (hMK : Proof.Gcm.AArch64.Pmull.MulKey) (gh : Gh8Ok)
    {tb : List Instr} {to sh : Bool} {s s₁ : State} {W O Tg : Addr} {tl : Nat}
    (o₁ : OpenInG Wn to (s.gpr .x0) W s.sp (s.gpr .x2) (s.gpr .x4) (s.gpr .x6) O Tg (s.gpr .x1).toNat
      (s.gpr .x3).toNat (s.gpr .x5).toNat (s.gpr .x7).toNat tl s s₁)
    (x12₁ : s₁.gpr .x12 = Tg) (hx₁ : ∀ r ∈ [Reg.x4, .x5, .x6, .x7], s₁.gpr r = s.gpr r)
    (hgh : ∀ (s' : State) {Y Dd S : Addr} {nb : Nat}, GhCall s' (s.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR Wn W) → Region.Sub ⟨S, 256⟩ (workR Wn W) →
      s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Frame [workR Wn W, ⟨O, (s.gpr .x7).toNat⟩] s.mem s'.mem →
      WP isa cl s' (GhPost s' (s.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb))
    (htb : TbForOP Wn tb (s.gpr .x0) W s.sp O (s.gpr .x7).toNat s) :
    WP isa (openSelS v.callees to tb cl sh) s₁ (OpenSPost to O Tg tl s) := by
  obtain hdk := dataOk_of o₁.dat
  obtain hnb : (s.gpr .x7).toNat + Wn ≤ 2 ^ 64 := len_of_disjoint hdk.w hdk.wrap o₁.lay.ww
  obtain doD : ∀ r ∈ ([] : List Region), (⟨O, (s.gpr .x7).toNat⟩ : Region).Disjoint r := by simp
  -- The branch on the tag length, and then `m`.
  obtain rest : ∀ {m : Prog isa} {s₄ : State}, OpenInG Wn to (s.gpr .x0) W s.sp (s.gpr .x2) (s.gpr .x4) (s.gpr .x6) O Tg
      (s.gpr .x1).toNat (s.gpr .x3).toNat (s.gpr .x5).toNat (s.gpr .x7).toNat tl s s₄ → s₄.gpr .x12 = Tg →
      (∀ r ∈ [Reg.x4, .x5, .x6, .x7], s₄.gpr r = s.gpr r) →
      (∀ {t : State}, OpenInG Wn to (s.gpr .x0) W s.sp (s.gpr .x2) (s.gpr .x4) (s.gpr .x6) O Tg (s.gpr .x1).toNat
          (s.gpr .x3).toNat (s.gpr .x5).toNat (s.gpr .x7).toNat tl s t →
        bytesAt t.mem W tl = bytesAt s.mem Tg tl → Spec.Gcm.tagLenOk tl = true →
        (∀ r ∈ [Reg.x4, .x5, .x6, .x7], t.gpr r = s.gpr r) →
        WP isa m t (OpenPostG Wn (s.gpr .x0) W s.sp (s.gpr .x2) (s.gpr .x4) O Tg (s.gpr .x1).toNat
          (s.gpr .x3).toNat (s.gpr .x5).toNat (s.gpr .x7).toNat tl (bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat)
          (fun m => bytesAt m O (s.gpr .x7).toNat = cond to (List.replicate (s.gpr .x7).toNat 0)
            (bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat)) s)) →
      WP isa (.seq tagLenOk (.seq (.ite (.zero .x .x9) (.seq (.block [imm .x0 0]) (wipeG to)) (.seq tagIn m))
        (.block restore))) s₄ (OpenSPost to O Tg tl s) := fun {m s₄} o₄ x12₄ hx₄ hm => by
    refine WP.mono (openRestWithFl_wp (fl := .seq (.block [imm .x0 0]) (wipeG to)) (m := m)
      (C := bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat)
      (F := fun m => bytesAt m O (s.gpr .x7).toNat = cond to (List.replicate (s.gpr .x7).toNat 0)
        (bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat)) o₄ x12₄ (fun o' _ _ hok => ?_)
      fun o' hT hok hx' => hm o' hT hok fun r hr => (hx' r hr).trans (hx₄ r hr)) fun _ h => h
    exact failG_ok o' hok
  unfold openSelS
  refine WP.seq (WP.mono (cond_ok (al := (s.gpr .x5).toNat) (nl := (s.gpr .x3).toNat)
    (by rw [hx₁ .x5 (by simp), ofNat_toNat']) (s.gpr .x5).isLt o₁.x24 (s.gpr .x3).isLt)
    fun s₂ ⟨x10₂, r₂⟩ => ?_)
  obtain o₂ := o₁.of_regs r₂
  obtain x12₂ : s₂.gpr .x12 = Tg := by rw [r₂.others _ (by decide), x12₁]
  obtain hx₂ : ∀ r ∈ [Reg.x4, .x5, .x6, .x7], s₂.gpr r = s.gpr r := fun r hr => by
    rw [r₂.others r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide), hx₁ r hr]
  by_cases hc : (s.gpr .x5).toNat ≤ 16 ∧ (s.gpr .x3).toNat = 12
  · refine WP.ite true (by rw [eval_zero x10₂ (by split <;> decide)]; simp [hc]) (fun _ => ?_) (fun h => by cases h)
    -- The three paths for TLS records, once the tag is read.
    obtain fastP : ∀ {s₄ : State}, OpenInG Wn to (s.gpr .x0) W s.sp (s.gpr .x2) (s.gpr .x4) (s.gpr .x6) O Tg
        (s.gpr .x1).toNat (s.gpr .x3).toNat (s.gpr .x5).toNat (s.gpr .x7).toNat tl s s₄ → s₄.gpr .x12 = Tg →
        (∀ r ∈ [Reg.x4, .x5, .x6, .x7], s₄.gpr r = s.gpr r) →
        WP isa (Impl.AesGcm.AArch64.Fast.openFastPG v.callees to cl) s₄ (OpenSPost to O Tg tl s) :=
      fun o₄ x12₄ hx₄ => rest o₄ x12₄ hx₄ fun o' hT hok hx =>
        openRunWithG_postE cl v hMK (ex := []) o' hc.2 (hx .x4 (by simp)) (by rw [hx .x5 (by simp), ofNat_toNat'])
          (hx .x6 (by simp)) (by rw [hx .x7 (by simp), ofNat_toNat']) hc.1 hT hok (by simp) (by simp) (by simp)
          fun s' _ _ _ _ c sY sS hr hw hsp hf _ => hgh s' c sY sS hr hw hsp (frame_wD hf)
    obtain fastS : ∀ {s₄ : State}, OpenInG Wn to (s.gpr .x0) W s.sp (s.gpr .x2) (s.gpr .x4) (s.gpr .x6) O Tg
        (s.gpr .x1).toNat (s.gpr .x3).toNat (s.gpr .x5).toNat (s.gpr .x7).toNat tl s s₄ → s₄.gpr .x12 = Tg →
        (∀ r ∈ [Reg.x4, .x5, .x6, .x7], s₄.gpr r = s.gpr r) →
        WP isa (Impl.AesGcm.AArch64.Stitch.openFastSG v.callees to tb cl) s₄ (OpenSPost to O Tg tl s) :=
      fun o₄ x12₄ hx₄ => rest o₄ x12₄ hx₄ fun o' hT hok hx =>
        WP.mono (openRunWithS_postX v cl hMK gh (ex := []) (I := fun _ => True) o' hc.2 (hx .x4 (by simp))
          (by rw [hx .x5 (by simp), ofNat_toNat']) (hx .x6 (by simp)) (by rw [hx .x7 (by simp), ofNat_toNat']) hc.1
          hT hok (by simp) (by simp) (by simp) (by simp) (fun _ _ => trivial)
          (fun s' _ _ _ _ hc sY sS hr hw hsp hf _ => WP.mono (hgh s' hc sY sS hr hw hsp hf) fun _ g => ⟨g, trivial⟩)
          htb.tbFor) fun _ q => q.1
    cases sh with
    | true =>
      simp only [↓reduceIte]
      refine WP.seq (WP.mono (shortThr_ok (n := (s.gpr .x7).toNat) s₂ (by rw [hx₂ .x7 (by simp), ofNat_toNat'])
        (by omega_using [hnb])) fun s₃ ⟨x9₃, r₃⟩ => ?_)
      obtain o₃ := o₂.of_regs r₃
      obtain x12₃ : s₃.gpr .x12 = Tg := by rw [r₃.others _ (by decide), x12₂]
      obtain hx₃ : ∀ r ∈ [Reg.x4, .x5, .x6, .x7], s₃.gpr r = s.gpr r := fun r hr => by
        rw [r₃.others r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide), hx₂ r hr]
      refine WP.ite _ (eval_zero x9₃ (by omega_using [])) (fun hz => ?_) (fun _ => ?_)
      · refine WP.seq (WP.mono (shortMin_ok (n := (s.gpr .x7).toNat) s₃ (by rw [hx₃ .x7 (by simp), ofNat_toNat'])
          (by omega_using [hnb])) fun s₄ ⟨x9₄, r₄⟩ => ?_)
        obtain o₄ := o₃.of_regs r₄
        obtain x12₄ : s₄.gpr .x12 = Tg := by rw [r₄.others _ (by decide), x12₃]
        obtain hx₄ : ∀ r ∈ [Reg.x4, .x5, .x6, .x7], s₄.gpr r = s.gpr r := fun r hr => by
          rw [r₄.others r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide), hx₃ r hr]
        refine WP.ite _ (eval_zero x9₄ (by omega_using [])) (fun _ => fastP o₄ x12₄ hx₄) (fun _ => ?_)
        unfold Impl.AesGcm.AArch64.Stitch.openShortFG
        refine rest o₄ x12₄ hx₄ fun o' hT hok hx => ?_
        obtain h96 := of_decide_eq_true hz
        rw [hc.2] at o' ⊢
        exact openShort_post gh o' (hx .x4 (by simp)) (by rw [hx .x5 (by simp), ofNat_toNat'])
          (hx .x6 (by simp)) (by rw [hx .x7 (by simp), ofNat_toNat']) hc.1 (by omega_using [h96]) hT hok
          fun u he hrd hwr hf => htb u he hrd hwr hf
      · refine WP.seq (WP.mono (Stitch.thr_ok s₃) fun s₄ ⟨_, r₄⟩ => ?_)
        obtain o₄ := o₃.of_regs r₄
        obtain x12₄ : s₄.gpr .x12 = Tg := by rw [r₄.others _ (by decide), x12₃]
        obtain hx₄ : ∀ r ∈ [Reg.x4, .x5, .x6, .x7], s₄.gpr r = s.gpr r := fun r hr => by
          rw [r₄.others r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide), hx₃ r hr]
        refine WP.ite _ (eval_zero (a := (s₄.gpr .x9).toNat) (by rw [ofNat_toNat']) (s₄.gpr .x9).isLt)
          (fun _ => fastP o₄ x12₄ hx₄) (fun _ => fastS o₄ x12₄ hx₄)
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      refine WP.seq (WP.mono (Stitch.thr_ok s₂) fun s₄ ⟨_, r₄⟩ => ?_)
      obtain o₄ := o₂.of_regs r₄
      obtain x12₄ : s₄.gpr .x12 = Tg := by rw [r₄.others _ (by decide), x12₂]
      obtain hx₄ : ∀ r ∈ [Reg.x4, .x5, .x6, .x7], s₄.gpr r = s.gpr r := fun r hr => by
        rw [r₄.others r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide), hx₂ r hr]
      refine WP.ite _ (eval_zero (a := (s₄.gpr .x9).toNat) (by rw [ofNat_toNat']) (s₄.gpr .x9).isLt)
        (fun _ => fastP o₄ x12₄ hx₄) (fun _ => fastS o₄ x12₄ hx₄)
  · refine WP.ite false (by rw [eval_zero x10₂ (by split <;> decide)]; simp [hc]) (fun h => by cases h) (fun _ => ?_)
    unfold openRestG
    exact rest o₂ x12₂ hx₂ fun o' hT hok _ => openMainG_post v to o' hT hok

/-- `vg_aes_gcm_open` with the interleaved path and the path for short
records (`sh`), `work` the stack argument `w`, for a `tb` that writes the
table without `H'` (`TbForOP`). -/
theorem openWithSh_wp {Wn : Nat} (v : GcmImpl) (cl : Prog isa) (hMK : Proof.Gcm.AArch64.Pmull.MulKey) (gh : Gh8Ok)
    {tb : List Instr} {w : Nat} (hw : w = 2 ∨ w = 3) {extra extraW : List Region}
    {s : State} (hs : openPreXW w extra s extraW)
    (hgh : ∀ (s' : State) {Y Dd S : Addr} {nb : Nat}, GhCall s' (s.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR Wn (stackArg s w)) → Region.Sub ⟨S, 256⟩ (workR Wn (stackArg s w)) →
      s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Frame [workR Wn (stackArg s w), ⟨s.gpr .x6, (s.gpr .x7).toNat⟩] s.mem s'.mem →
      WP isa cl s' (GhPost s' (s.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb))
    (htb : TbForOP Wn tb (s.gpr .x0) (stackArg s w) s.sp (s.gpr .x6) (s.gpr .x7).toNat s) :
    WP isa (Impl.AesGcm.AArch64.Stitch.openWithSG v.callees false w tb cl true) s fun s' =>
      GprAbi s s' ∧ openAArch64.post s s' := by
  rw [openWithSG_eq, show openEntryG false w = oneEntry (8 * w) ++ stashArg 8 ++ ([.ldrSp .x12 0] : List Instr) by
    simp only [openEntryG, Bool.cond_false, List.append_nil]]
  refine WP.seq (WP.mono (WP.gprs (rs := [.x4, .x5, .x6, .x7]) (openEntry_ok hw hs)
    (by rcases hw with rfl | rfl <;> decide) (by rcases hw with rfl | rfl <;> decide))
    fun s₁ ⟨⟨o₁, x12₁⟩, hx₁⟩ => ?_)
  exact WP.mono (openSelS_wp v cl hMK gh o₁ x12₁ hx₁ hgh htb) fun _ h => h

/-- `vg_aes_gcm_open_to` with the interleaved path and the path for short
records (`sh`), `work` the stack argument `w`, for a `tb` that writes the
table without `H'` (`TbForOP`), in one pass. -/
theorem openToWithSh_wp {Wn : Nat} (v : GcmImpl) (cl : Prog isa) (hMK : Proof.Gcm.AArch64.Pmull.MulKey) (gh : Gh8Ok)
    {tb : List Instr} {w : Nat} (hw : w = 4 ∨ w = 5) {extra extraW : List Region}
    {s : State} (hs : openToPreXW w extra s extraW)
    (hgh : ∀ (s' : State) {Y Dd S : Addr} {nb : Nat}, GhCall s' (s.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR Wn (stackArg s w)) → Region.Sub ⟨S, 256⟩ (workR Wn (stackArg s w)) →
      s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Frame [workR Wn (stackArg s w), ⟨stackArg s 0, (s.gpr .x7).toNat⟩] s.mem s'.mem →
      WP isa cl s' (GhPost s' (s.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb))
    (htb : TbForOP Wn tb (s.gpr .x0) (stackArg s w) s.sp (stackArg s 0) (s.gpr .x7).toNat s) :
    WP isa (Impl.AesGcm.AArch64.Stitch.openWithSG v.callees true w tb cl true) s fun s' =>
      GprAbi s s' ∧ openToPostOf s s' := by
  rw [openWithSG_eq]
  refine WP.seq (WP.mono (WP.gprs (rs := [.x4, .x5, .x6, .x7]) (openEntryTo_ok (by omega_using [hw]) hs)
    (by rcases hw with rfl | rfl <;> decide) (by rcases hw with rfl | rfl <;> decide))
    fun s₁ ⟨⟨o₁, x12₁⟩, hx₁⟩ => ?_)
  exact WP.mono (openSelS_wp v cl hMK gh o₁ x12₁ hx₁ hgh htb) fun _ h => h

end VG.Proof.AesGcm.AArch64.Fast
