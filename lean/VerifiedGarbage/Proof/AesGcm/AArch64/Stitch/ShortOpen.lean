module

import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.ShortSeal
public import VerifiedGarbage.Proof.AesGcm.AArch64.Open
import VerifiedGarbage.Proof.AesGcm.AArch64.Cmp
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
public import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.Tables
import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.ShortCopy
import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.ShortAes
import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.ShortBytes
import VerifiedGarbage.Proof.Gcm.Short

/-!
# AES-GCM on AArch64, short records: `openShort`

Untrusted: everything here is checked by Lean. `openShort` opens a record of
at most 96 bytes as `open` does (`openShort_post`), once the received tag is
at `W`: `B₂` gets the ciphertext and is hashed before `B₁` is decrypted
(`b2_layout`, `ghash_lead`, `b1_gctr`), the tag (GHASH XORed with block
`p − 1` of `B₁`, `CIPH_K(J₀)`: `b1_j0`) is compared with the received one
(`cmp_ok`), and the plaintext is copied to the text only if they are equal.
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
  rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl <;> rfl

/-- `openShort` up to the branch on the tags. -/
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

/-- The rest of `openShort`: the plaintext to the text if the tags are equal, and the result. -/
def openShortB : Prog isa :=
  .seq (.ite (.zero .x .x24) (.block []) Impl.AesGcm.AArch64.Stitch.plainOut) (.block [mov .x0 .x24])

/-- `openShort` is `openShortA` then `openShortB`. -/
theorem openShort_split (tb : List Instr) :
    PEq (.seq (openShortA tb) openShortB) (Impl.AesGcm.AArch64.Stitch.openShort tb) := by
  unfold openShortA openShortB Impl.AesGcm.AArch64.Stitch.openShort
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
the text as it was. -/
structure ShortMid (Ctx W SP Np A D Tg : Addr) (R al n tl : Nat) (s₀ u : State) : Prop where
  env : Env Ctx (W + BitVec.ofNat 64 16) W SP u
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

/-- `openShortA`, from the state `open` leaves once the received tag is at
`W`, for a record of at most 96 bytes. -/
theorem openShortA_ok (gh : Gh8Ok) {tb : List Instr} {Ctx W SP Np A D Tg : Addr} {R al n tl : Nat}
    {s₀ t : State} (o : OpenIn Ctx W SP Np A D Tg R 12 al n tl s₀ t)
    (h4 : t.gpr .x4 = A) (h5 : t.gpr .x5 = BitVec.ofNat 64 al) (h6 : t.gpr .x6 = D)
    (h7 : t.gpr .x7 = BitVec.ofNat 64 n) (h16 : al ≤ 16) (hhi : n ≤ 96)
    (hT : bytesAt t.mem W tl = bytesAt s₀.mem Tg tl) (hok : Spec.Gcm.tagLenOk tl = true)
    (htb : ∀ u : State, Env Ctx (W + BitVec.ofNat 64 16) W SP u → u.rd = s₀.rd → u.wr = s₀.wr →
      Frame [workR W, ⟨D, n⟩] s₀.mem u.mem → WP isa (.block tb) u (Stitch.TblPost W (ctxH s₀.mem Ctx) u)) :
    WP isa (openShortA tb) t (ShortMid Ctx W SP Np A D Tg R al n tl s₀) := by
  have L := o.lay
  have he₁ := o.env
  have hRb := o.rounds
  have perm := he₁.perm
  have ddW := o.ddW
  have daW := o.daW
  have dcW := o.dcW
  obtain ⟨hc₀, hH₀, hN₀, hA₀, hD₀⟩ := o.vals
  have hnlt : n < 2 ^ 64 := o.dat.ok.lt
  have htl : tl ≤ 16 := by simp [Spec.Gcm.tagLenOk] at hok; omega
  have sub16 : Region.Sub ⟨W + BitVec.ofNat 64 16, 80⟩ (workR W) := Lay.wSub (by decide)
  have hJ : J0In Ctx (W + BitVec.ofNat 64 16) W SP t.gpr (ctxH s₀.mem Ctx) Np 12 t :=
    ⟨he₁, fun _ _ => rfl, o.x23, o.x24, o.x26, o.x27, o.non, hH₀⟩
  generalize hc : (n + 15) / 16 = c
  have hc6 : c ≤ 6 := by omega
  have hcn : n ≤ 16 * c := by omega
  have hcn' : 16 * c ≤ n + 15 := by omega
  unfold openShortA Impl.AesGcm.AArch64.Stitch.shortPre
  -- `J₀`, the first counter block, and the lengths.
  refine WP.seq (WP.seq (WP.block_append_iff.mpr (WP.block_append_iff.mpr
    (WP.mono (WP.with_rdwr (WP.block_and (j012_ok L hJ) (j012_others hJ))) fun s₂ ⟨⟨h₂, o₂⟩, rd₂, wr₂⟩ =>
      WP.mono (WP.with_rdwr (WP.block_and (initState_ok L h₂) (initState_others h₂.env)))
        fun s₃ ⟨⟨h₃, o₃⟩, rd₃, wr₃⟩ => ?_))))
  rw [hN₀] at h₃
  have o₁₃ : ∀ r ∉ [Reg.x9, .x10, .x11, .x12], s₃.gpr r = t.gpr r := fun r hr => by rw [o₃ r hr, o₂ r hr]
  have F₃ : Frame [workR W, ⟨D, n⟩] s₀.mem s₃.mem := by
    have wE : ∀ {r : Region}, Region.Sub r (workR W) → ∃ r' ∈ [workR W, (⟨D, n⟩ : Region)], Region.Sub r r' :=
      fun h => ⟨_, List.mem_cons_self .., h⟩
    have j0W : ∀ r ∈ j0Frame (W + BitVec.ofNat 64 16) W, Region.Sub r (workR W) := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact sub16
      · exact Lay.wSub (by decide)
      · exact Lay.wSub (by decide)
    exact (o.fr.sub fun r hr => wE (entry16_work W r hr)).trans (h₃.frame.sub fun r hr => wE (j0W r hr))
  refine WP.mono (Stitch.shortLen_ok (n := n) (D := D) (al := al) s₃ (by rw [o₁₃ _ (by decide), h7])
    (by rw [o₁₃ _ (by decide), h6]) (by rw [o₁₃ _ (by decide), h5]) (by omega))
    fun t₀ ⟨x26₅, x27₅, x24₅, x25₅, g₅, m₅, v₅, sp₅, rd₅, wr₅⟩ => ?_
  rw [hc] at x25₅
  have he₅ : Env Ctx (W + BitVec.ofNat 64 16) W SP t₀ := h₃.env.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact g₅ _ (by decide) (by decide) (by decide) (by decide)) sp₅ rd₅ wr₅
  -- The table.
  refine WP.seq (WP.mono (htb t₀ he₅ (by rw [rd₅, rd₃, rd₂, o.rd₀]) (by rw [wr₅, wr₃, wr₂, o.wr₀])
    (by rw [m₅]; exact F₃)) fun s₄ ⟨tbl₄, ft₄, g₄, sp₄, rd₄, wr₄⟩ => ?_)
  rw [m₅] at ft₄
  have he₄ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₄ := he₅.keep (fun r hr => g₄ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide)) sp₄ rd₄ wr₄
  -- The buffers zeroed.
  refine WP.mono (Stitch.zeroBufs_ok (c := c) hc6 s₄ he₄.x19 (by rw [g₄ _ (by decide), x25₅])
    he₄.perm.w) fun s₆ ⟨m₆, g₆, sp₆, rd₆, wr₆⟩ => ?_
  have he₆ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₆ := he₄.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact g₆ _ (by decide)) sp₆ rd₆ wr₆
  -- What `shortLen` and the entry leave, kept since.
  have k₆ : ∀ r ∉ [Reg.x5, .x9, .x10, .x11, .x12, .x24, .x25, .x26, .x27], s₆.gpr r = t.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g₆ _ hr.2.1, g₄ _ hr.1, g₅ _ hr.2.2.2.2.2.1 hr.2.2.2.2.2.2.1 hr.2.2.2.2.2.2.2.1 hr.2.2.2.2.2.2.2.2,
      o₁₃ _ (by simp [hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1])]
  have x25₆ : s₆.gpr .x25 = BitVec.ofNat 64 (16 * c) := by rw [g₆ _ (by decide), g₄ _ (by decide), x25₅]
  have x26₆ : s₆.gpr .x26 = BitVec.ofNat 64 n := by rw [g₆ _ (by decide), g₄ _ (by decide), x26₅]
  have x27₆ : s₆.gpr .x27 = D := by rw [g₆ _ (by decide), g₄ _ (by decide), x27₅]
  have x24₆ : s₆.gpr .x24 = BitVec.ofNat 64 al := by rw [g₆ _ (by decide), g₄ _ (by decide), x24₅]
  have x4₆ : s₆.gpr .x4 = A := by rw [k₆ _ (by decide), h4]
  have rd₆' : s₆.rd = s₀.rd := by rw [rd₆, rd₄, rd₅, rd₃, rd₂, o.rd₀]
  have wr₆' : s₆.wr = s₀.wr := by rw [wr₆, wr₄, wr₅, wr₃, wr₂, o.wr₀]
  have x22₆ : s₆.gpr .x22 = BitVec.ofNat 64 R := by rw [k₆ _ (by decide), o.x22]
  have x28₆ : s₆.gpr .x28 = BitVec.ofNat 64 tl := by rw [k₆ _ (by decide), o.x28]
  have hw : ∀ {u : State}, u.wr = s₀.wr → Covers [⟨W, 2560⟩] u.wr := fun h => by rw [h, ← o.wr₀]; exact perm.w
  -- The ciphertext, to block `p` of `B₁`.
  unfold Impl.AesGcm.AArch64.Stitch.textIn
  refine WP.seq (WP.seq ?_)
  rw [WP.block_append_iff]
  obtain ⟨t₁, run₁, x11₁, g₁', m₁', _, sp₁', rd₁', wr₁'⟩ := Stitch.atP_ok (c := c) .x11
    Impl.AesGcm.AArch64.Stitch.b1O 1 (by decide) (by unfold Impl.AesGcm.AArch64.Stitch.b1O; omega) s₆ he₆.x19
    x25₆ (by decide)
  refine WP.of_runBlock ⟨t₁, run₁, ?_⟩
  obtain ⟨s₇, run₇, x12₇, x13₇, r₇⟩ : ∃ s₇, runBlock isa [mov .x12 .x27, mov .x13 .x26] t₁ = some s₇ ∧
      s₇.gpr .x12 = D ∧ s₇.gpr .x13 = BitVec.ofNat 64 n ∧ Regs [.x12, .x13] t₁ s₇ := by
    refine ⟨_, by arun [], ?_⟩
    exact ⟨by simp [gpr_write, g₁' .x27 (by decide), x27₆], by simp [gpr_write, g₁' .x26 (by decide), x26₆],
      ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
  refine WP.of_runBlock ⟨s₇, run₇, ?_⟩
  have x11₇ : s₇.gpr .x11 = W + BitVec.ofNat 64 (880 - 16 * c) := by
    rw [r₇.others _ (by decide), x11₁]; rfl
  have rd₇ : s₇.rd = s₀.rd := by rw [r₇.rd, rd₁', rd₆']
  have wr₇ : s₇.wr = s₀.wr := by rw [r₇.wr, wr₁', wr₆']
  have m₇ : s₇.mem = s₆.mem := by rw [r₇.mem, m₁']
  refine WP.mono (Stitch.copyQ_ok s₇ ⟨x12₇, x11₇, x13₇, by omega,
    by rw [rd₇, wr₇, ← o.rd₀, ← o.wr₀]; exact o.dat.ok.1,
    by rw [wr₇]; exact covers_off (hw rfl) (by omega) (by decide), ddW.sub_right (Lay.wSub (by omega))⟩)
    fun s₈ ⟨m₈, g₈, sp₈, rd₈, wr₈⟩ => ?_
  -- The registers kept since `zeroBufs`.
  have kk : ∀ {u v : State} {rs : List Reg}, (∀ r, r ∉ rs → v.gpr r = u.gpr r) →
      (∀ r ∈ [Reg.x4, .x19, .x20, .x21, .x22, .x24, .x25, .x26, .x27, .x28], r ∉ rs) →
      (∀ r ∈ [Reg.x4, .x19, .x20, .x21, .x22, .x24, .x25, .x26, .x27, .x28], u.gpr r = s₆.gpr r) →
      ∀ r ∈ [Reg.x4, .x19, .x20, .x21, .x22, .x24, .x25, .x26, .x27, .x28], v.gpr r = s₆.gpr r :=
    fun hg hd hu r hr => by rw [hg r (hd r hr), hu r hr]
  have k₈ : ∀ r ∈ [Reg.x4, .x19, .x20, .x21, .x22, .x24, .x25, .x26, .x27, .x28], s₈.gpr r = s₆.gpr r :=
    kk g₈ (by decide) (kk r₇.others (by decide) (kk (rs := [.x11]) (fun r h => g₁' r (by simpa using h))
      (by decide) fun _ _ => rfl))
  have he₈ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₈ := he₆.keep (fun r hr => k₈ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp))
    (by rw [sp₈, r₇.sp, sp₁']) (by rw [rd₈, r₇.rd, rd₁']) (by rw [wr₈, r₇.wr, wr₁'])
  -- The ciphertext, to `B₂`.
  refine WP.seq (WP.mono (Stitch.ctToB2_ok' hc6 hcn s₈ he₈.x19 (by rw [k₈ .x25 (by simp), x25₆])
    (by rw [k₈ .x26 (by simp), x26₆]) he₈.perm.w) fun s₉ ⟨m₉, g₉, sp₉, rd₉, wr₉⟩ => ?_)
  have k₉ := kk g₉ (by decide) k₈
  have he₉ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₉ := he₈.keep (fun r hr => g₉ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide)) sp₉ rd₉ wr₉
  have rd₉' : s₉.rd = s₀.rd := by rw [rd₉, rd₈, rd₇]
  have wr₉' : s₉.wr = s₀.wr := by rw [wr₉, wr₈, wr₇]
  -- The additional data, to `B₂`.
  refine WP.seq (WP.mono (Stitch.aadIn_ok (A := A) (al := al) hc6 s₉ he₉.x19
    (by rw [k₉ .x25 (by simp), x25₆]) he₉.perm.w (by rw [k₉ .x4 (by simp), x4₆])
    (by rw [k₉ .x24 (by simp), x24₆]) h16
    (by rw [rd₉', wr₉', ← o.rd₀, ← o.wr₀]; exact o.aad.1) (daW.sub_right (Lay.wSub (by omega))))
    fun s₁₀ ⟨m₁₀, g₁₀, sp₁₀, rd₁₀, wr₁₀⟩ => ?_)
  have k₁₀ := kk g₁₀ (by decide) k₉
  have he₁₀ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₁₀ := he₉.keep (fun r hr => g₁₀ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide)) sp₁₀ rd₁₀ wr₁₀
  -- The lengths block and GHASH.
  simp only [List.append_assoc]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (Stitch.lensB_ok (al := al) (n := n) s₁₀ he₁₀.x19 he₁₀.perm.w (by rw [k₁₀ .x24 (by simp), x24₆])
    (by rw [k₁₀ .x26 (by simp), x26₆]) (by omega) hnlt) fun s₁₁ ⟨lens₁₁, fL₁₁, og₁₁, sp₁₁, rd₁₁, wr₁₁, _⟩ => ?_
  have k₁₁ := kk (rs := [.x9, .x10]) og₁₁ (by decide) k₁₀
  have he₁₁ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₁₁ := he₁₀.keep (fun r hr => og₁₁ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide)) sp₁₁ rd₁₁ wr₁₁
  -- What the writes since the table keep.
  let BR : Region := ⟨W + BitVec.ofNat 64 768, 256⟩
  have one : ∀ {m m' : Mem} {q : Addr} {k : Nat}, Frame [⟨q, k⟩] m m' → Region.Sub ⟨q, k⟩ BR → Frame [BR] m m' :=
    fun h hs => h.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, hs⟩
  have sB : ∀ {e k : Nat}, 768 ≤ e → e + k ≤ 1024 → Region.Sub ⟨W + BitVec.ofNat 64 e, k⟩ BR :=
    fun h₁ h₂ => Offset.sub W h₁ (by omega)
  have lb := Proof.AesCcm.length_bytesAt
  have F₄₁₁ : Frame [BR] s₄.mem s₁₁.mem := by
    have a₁ : Frame [BR] s₄.mem s₆.mem := by
      rw [m₆]
      exact (one (writeBytes_frame' _ List.length_replicate) (sB (by decide) (by decide))).trans
        (one (writeBytes_frame' _ List.length_replicate) (sB (by omega) (by omega)))
    have a₂ : Frame [BR] s₆.mem s₈.mem := by
      rw [m₈, m₇]; exact one (writeBytes_frame' _ (lb _ _ _)) (sB (by omega) (by omega))
    have a₃ : Frame [BR] s₈.mem s₉.mem := by
      rw [m₉]
      exact (one (writeBytes_frame' _ (lb _ _ _)) (sB (by omega) (by omega))).trans
        (one (writeBytes_frame' _ List.length_replicate) (sB (by omega) (by omega)))
    have a₄ : Frame [BR] s₉.mem s₁₀.mem := by
      rw [m₁₀]; exact one (writeBytes_frame' _ (lb _ _ _)) (sB (by omega) (by omega))
    exact (((a₁.trans a₂).trans a₃).trans a₄).trans (one fL₁₁ (sB (by decide) (by decide)))
  have one1 : ∀ {X r : Region}, X.Disjoint r → ∀ r' ∈ [r], X.Disjoint r' := fun h r' hr' => by
    simp only [List.mem_singleton] at hr'; subst hr'; exact h
  have dWW : ∀ {d k e j : Nat}, d + k ≤ e ∨ e + j ≤ d → d + k ≤ 2560 → e + j ≤ 2560 →
      (⟨W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 e, j⟩ :=
    fun h h₁ h₂ => Offset.disjoint W h (by omega) (by omega)
  have tbl₁₁ : TblOk s₁₁.mem W (ctxH s₀.mem Ctx) :=
    tblOk_frame tbl₄ F₄₁₁ (one1 (dWW (.inl (by decide)) (by decide) (by decide)))
  rw [WP.block_append_iff]
  refine WP.mono (Stitch.shortGh_ok gh s₁₁ he₁₁.x19 tbl₁₁ (covers_left he₁₁.perm.w))
    fun s₁₂ ⟨y₁₂, g₁₂, m₁₂, sp₁₂, rd₁₂, wr₁₂⟩ => ?_
  have k₁₂ := kk (rs := [.x9, .x12]) (fun r h => g₁₂ r (fun e => h (by simp [e])) (fun e => h (by simp [e])))
    (by decide) k₁₁
  have he₁₂ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₁₂ := he₁₁.keep (fun r hr => k₁₂ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp) |>.trans (k₁₁ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp)).symm) sp₁₂ rd₁₂ wr₁₂
  -- The counter, and one pass of AES over `B₁`.
  refine WP.mono (Stitch.shortCtr_ok (W := W) (St := W + BitVec.ofNat 64 16) hc6 s₁₂ he₁₂.x19 he₁₂.x20
    (by rw [k₁₂ .x25 (by simp), x25₆]) (he₁₂.perm.stR (by decide)))
    fun s₁₃ ⟨x10₁₃, x9₁₃, g₁₃, m₁₃, v₁₃, sp₁₃, rd₁₃, wr₁₃⟩ => ?_
  have k₁₃ := kk (rs := [.x9, .x10]) (fun r h => g₁₃ r (fun e => h (by simp [e])) (fun e => h (by simp [e])))
    (by decide) k₁₂
  have he₁₃ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₁₃ := he₁₂.keep (fun r hr => g₁₃ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide)) sp₁₃ rd₁₃ wr₁₃
  have hp₁₃ : Proof.Gcm.AArch64.Stitch.APre R 0 (2 ^ 32 + c - 7) s₁₃ := {
    rounds := hRb
    o_le := by decide
    keys := fun r hr => by
      rw [Proof.Gcm.AArch64.Stitch.kp, he₁₃.x21]
      exact in_off he₁₃.perm.ctx (by omega) (by decide)
    ctr := by
      rw [Proof.Gcm.AArch64.Stitch.cbA, he₁₃.x20, add_ofNat_zero]
      exact he₁₃.perm.stR (by decide)
    data := fun j hj => by
      rw [x9₁₃, Offset.add_add]
      exact he₁₃.perm.wR (by unfold Impl.AesGcm.AArch64.Stitch.b1O; omega)
    x10 := by
      rw [x10₁₃]
      simp only [Proof.Gcm.AArch64.Stitch.c0, Proof.Gcm.AArch64.Stitch.cbk, Proof.Gcm.AArch64.Stitch.cbA, m₁₃,
        he₁₃.x20] }
  refine WP.seq (WP.mono (Stitch.shortAesB_ok s₁₃ hp₁₃ (by rw [k₁₃ .x22 (by simp), x22₆]) x9₁₃
    (covers_off he₁₃.perm.w (by decide) (by decide))) fun s₁₄ ⟨ks₁₄, f₁₄, g₁₄, sp₁₄, rd₁₄, wr₁₄, y₁₄⟩ => ?_)
  have k₁₄ := kk g₁₄ (by decide) k₁₃
  have he₁₄ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₁₄ := he₁₃.keep (fun r hr => g₁₄ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide)) sp₁₄ rd₁₄ wr₁₄
  -- The tag, at `W + uO`.
  refine WP.seq (WP.mono (Stitch.shortTagAt_ok (W := W) (o := 112)
    (g := Spec.Gcm.ghashFrom (ctxH s₀.mem Ctx) 0 ((List.range 8).map fun j =>
      Spec.Gcm.blockAt s₁₁.mem (W + BitVec.ofNat 64 (Impl.AesGcm.AArch64.Stitch.b2O + 16 * j))))
    (.inr rfl) hc6 s₁₄ he₁₄.x19
    (by rw [k₁₄ .x25 (by simp), x25₆]) (by rw [y₁₄, v₁₃]; exact y₁₂) he₁₄.perm.w)
    fun s₁₅ ⟨tag₁₅, fT₁₅, g₁₅, sp₁₅, rd₁₅, wr₁₅⟩ => ?_)
  have k₁₅ := kk (rs := [.x9]) (fun r h => g₁₅ r (fun e => h (by simp [e]))) (by decide) k₁₄
  have he₁₅ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₁₅ := he₁₄.keep (fun r hr => g₁₅ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide)) sp₁₅ rd₁₅ wr₁₅
  -- The tags compared.
  refine WP.seq (WP.mono (WP.with_rdwr (WP.gprs (rs := [.x25, .x26, .x27]) (cmp_ok L (k := s₁₅.gpr) he₁₅
      (fun _ _ => rfl) (by rw [k₁₅ .x28 (by simp), x28₆]) htl) (by decide) (by decide)))
    fun s₁₆ ⟨⟨⟨x10₁₆, he₁₆, _, _, fC₁₆⟩, gk₁₆⟩, rd₁₆, wr₁₆⟩ => ?_)
  -- The bytes, through the writes.
  have selfB : ∀ (m : Mem) (q : Addr) (xs : List Byte) {k : Nat}, xs.length = k → k < 2 ^ 64 →
      bytesAt (writeBytes m q xs) q k = xs := fun m q xs _ hk hk' => by
    subst hk; exact bytesAt_writeBytes_self m q xs hk'
  have wf : ∀ (m : Mem) (q : Addr) (xs : List Byte) {k : Nat}, xs.length = k →
      Frame [⟨q, k⟩] m (writeBytes m q xs) := fun m _ _ _ hk => writeBytes_frame' m hk
  have dDW : ∀ {e j : Nat}, e + j ≤ 2560 → (⟨D, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 e, j⟩ :=
    fun h => ddW.sub_right (Lay.wSub h)
  have oneW : ∀ {m m' : Mem} {rs : List Region}, Frame rs m m' → (∀ r ∈ rs, Region.Sub r (workR W)) →
      Frame [workR W] m m' := fun h hs => h.sub fun r hr => ⟨_, List.mem_singleton_self _, hs r hr⟩
  have sW1 : ∀ {e k : Nat}, e + k ≤ 2560 → ∀ r ∈ [(⟨W + BitVec.ofNat 64 e, k⟩ : Region)], Region.Sub r (workR W) :=
    fun h r hr => by simp only [List.mem_singleton] at hr; subst hr; exact Lay.wSub h
  have Ft₄ : Frame [workR W] t.mem s₄.mem := by
    refine (oneW h₃.frame fun r hr => ?_).trans (oneW ft₄ (sW1 (by decide)))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact sub16
    · exact Lay.wSub (by decide)
    · exact Lay.wSub (by decide)
  have Ft₁₁ : Frame [workR W] t.mem s₁₁.mem := Ft₄.trans (oneW F₄₁₁ (sW1 (by decide)))
  have F₁₁₁₇ : Frame [workR W] s₁₁.mem s₁₆.mem := by
    rw [← m₁₂, ← m₁₃]
    exact ((oneW f₁₄ (sW1 (by decide))).trans (oneW fT₁₅ (sW1 (by decide)))).trans (oneW fC₁₆ (sW1 (by decide)))
  -- The text, unchanged so far.
  have hDt : bytesAt s₁₆.mem D n = bytesAt s₀.mem D n := by
    rw [bytesAt_frame (Ft₁₁.trans F₁₁₁₇) (one1 ddW) (by omega), hD₀]
  -- The key schedule and the counter block.
  have hsch : Proof.Gcm.AArch64.Stitch.sch R s₁₃ = bytesAt t.mem Ctx (16 * (R + 1)) := by
    have dC : (⟨Ctx, 16 * (R + 1)⟩ : Region).Disjoint (workR W) := dcW.sub_left (Region.sub_prefix (by omega))
    simp only [Proof.Gcm.AArch64.Stitch.sch, Proof.Gcm.AArch64.Stitch.kp, he₁₃.x21, m₁₃, m₁₂]
    rw [bytesAt_frame Ft₁₁ (one1 dC) (by omega)]
  have hciph : Spec.Gcm.aesWith R (Proof.Gcm.AArch64.Stitch.sch R s₁₃) = ctxCiph s₀.mem Ctx R := by
    rw [hsch]; exact hc₀
  generalize hJ0 : Spec.Gcm.j0 (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np 12) = J
  have cb₃ := h₃.cb
  rw [hJ0] at cb₃
  simp only [Offset.add_add] at cb₃
  have hcb : Proof.Gcm.AArch64.Stitch.cbk s₁₃ = inc32 J := by
    simp only [Proof.Gcm.AArch64.Stitch.cbk, Proof.Gcm.AArch64.Stitch.cbA, he₁₃.x20, Offset.add_add, m₁₃, m₁₂]
    rw [blockAt_frame F₄₁₁ (one1 (dWW (.inl (by decide)) (by decide) (by decide))),
      blockAt_frame ft₄ (one1 (dWW (.inl (by decide)) (by decide) (by decide))), cb₃]
  -- `B₁` before the pass: the ciphertext at block `p`, zeros at block `p − 1`.
  simp only [Impl.AesGcm.AArch64.Stitch.b2O, Impl.AesGcm.AArch64.Stitch.b1O] at m₆ ks₁₄ y₁₂ f₁₄ tag₁₅
  have B₁₁ : ∀ {e k : Nat}, 768 ≤ e → e + k ≤ 896 →
      bytesAt s₁₃.mem (W + BitVec.ofNat 64 e) k = bytesAt s₈.mem (W + BitVec.ofNat 64 e) k := fun h₁ h₂ => by
    rw [m₁₃, m₁₂, bytesAt_frame fL₁₁ (one1 (dWW (.inl (by omega)) (by omega) (by decide))) (by omega), m₁₀,
      bytesAt_frame (wf _ _ _ (lb _ _ _)) (one1 (dWW (.inl (by omega)) (by omega) (by omega))) (by omega), m₉,
      bytesAt_frame (wf _ _ _ List.length_replicate) (one1 (dWW (.inl (by omega)) (by omega) (by omega))) (by omega),
      bytesAt_frame (wf _ _ _ (lb _ _ _)) (one1 (dWW (.inl (by omega)) (by omega) (by omega))) (by omega)]
  have hP : bytesAt s₁₃.mem (W + BitVec.ofNat 64 768 + BitVec.ofNat 64 (16 * (7 - c))) n = bytesAt s₀.mem D n := by
    rw [Offset.add_add, show 768 + 16 * (7 - c) = 880 - 16 * c by omega, B₁₁ (by omega) (by omega), m₈,
      selfB _ _ _ (lb _ _ _) (by omega), m₇, m₆,
      bytesAt_frame (wf _ _ _ List.length_replicate) (one1 (dDW (by omega))) (by omega),
      bytesAt_frame (wf _ _ _ List.length_replicate) (one1 (dDW (by decide))) (by omega),
      bytesAt_frame Ft₄ (one1 ddW) (by omega), hD₀]
  have hz₁₃ : bytesAt s₁₃.mem (W + BitVec.ofNat 64 768 + BitVec.ofNat 64 (16 * (6 - c))) 16 = zeros 16 := by
    rw [Offset.add_add, show 768 + 16 * (6 - c) = 864 - 16 * c by omega, B₁₁ (by omega) (by omega), m₈,
      bytesAt_frame (wf _ _ _ (lb _ _ _)) (one1 (dWW (.inl (by omega)) (by omega) (by omega))) (by decide), m₇, m₆,
      selfB _ _ _ List.length_replicate (by decide)]
    rfl
  -- After the pass: the plaintext, and `CIPH_K(J₀)`.
  rw [hcb] at ks₁₄
  have hPt : bytesAt s₁₄.mem (W + BitVec.ofNat 64 (880 - 16 * c)) n =
      gctr (ctxCiph s₀.mem Ctx R) (inc32 J) (bytesAt s₀.mem D n) := by
    have := Stitch.b1_gctr hcn hc6 ks₁₄ hP
    rw [Offset.add_add, show 768 + 16 * (7 - c) = 880 - 16 * c by omega, hciph] at this
    exact this
  have hE : blockAt s₁₄.mem (W + BitVec.ofNat 64 (864 - 16 * c)) = ctxCiph s₀.mem Ctx R J := by
    have := Stitch.b1_j0 hc6 ks₁₄ hz₁₃
    rw [Offset.add_add, show 768 + 16 * (6 - c) = 864 - 16 * c by omega, hciph] at this
    exact this
  -- What `B₂` holds, and its GHASH.
  have hZ₆ : bytesAt s₆.mem (W + BitVec.ofNat 64 896) 128 = zeros 128 := by
    rw [m₆, bytesAt_frame (wf _ _ _ List.length_replicate) (one1 (dWW (.inr (by omega)) (by decide) (by omega)))
      (by decide), selfB _ _ _ List.length_replicate (by decide)]
    rfl
  have hA₉ : bytesAt s₉.mem A al = bytesAt s₀.mem A al := by
    have dA : ∀ {e j : Nat}, e + j ≤ 2560 → (⟨A, al⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 e, j⟩ :=
      fun h => daW.sub_right (Lay.wSub h)
    rw [m₉, bytesAt_frame (wf _ _ _ List.length_replicate) (one1 (dA (by omega))) (by omega),
      bytesAt_frame (wf _ _ _ (lb _ _ _)) (one1 (dA (by omega))) (by omega), m₈,
      bytesAt_frame (wf _ _ _ (lb _ _ _)) (one1 (dA (by omega))) (by omega), m₇, m₆,
      bytesAt_frame (wf _ _ _ List.length_replicate) (one1 (dA (by omega))) (by omega),
      bytesAt_frame (wf _ _ _ List.length_replicate) (one1 (dA (by decide))) (by omega),
      bytesAt_frame Ft₄ (one1 daW) (by omega), hA₀]
  have fY : Frame [⟨W + BitVec.ofNat 64 (880 - 16 * c), n⟩] s₆.mem s₈.mem := by
    rw [m₈, m₇]; exact wf _ _ _ (lb _ _ _)
  have L2 := Stitch.b2_layout (G := W + BitVec.ofNat 64 896) (c := c) (n := n)
    (Q := bytesAt s₈.mem (W + BitVec.ofNat 64 (880 - 16 * c)) (16 * c)) (A := bytesAt s₉.mem A al)
    (lens := Proof.Gcm.lensBlock al n) (mZ := s₆.mem) (mY := s₈.mem) (mL := s₁₁.mem) hc6 hcn
    (by omega) (lb _ _ _) (by rw [lb]; exact h16) hZ₆ fY
    (one1 (dWW (.inr (by omega)) (by decide) (by omega)))
    (by
      simp only [Offset.add_add]
      rw [show 896 + (112 - 16 * c) = 1008 - 16 * c by omega, show 896 + (112 - 16 * c + n) = 1008 - 16 * c + n by omega,
        show 896 + (96 - 16 * c) = 992 - 16 * c by omega, ← m₉, ← m₁₀]
      exact fL₁₁)
    (by rw [Offset.add_add]; exact lens₁₁)
  have hC₈ : bytesAt s₈.mem (W + BitVec.ofNat 64 (880 - 16 * c)) n = bytesAt s₀.mem D n := by
    have h := hP
    rw [Offset.add_add, show 768 + 16 * (7 - c) = 880 - 16 * c by omega] at h
    rw [← B₁₁ (e := 880 - 16 * c) (k := n) (by omega) (by omega)]; exact h
  rw [← Proof.AesCcm.bytesAt_prefix _ _ (show n ≤ 16 * c from hcn), hC₈, hA₉,
    show 16 * c - n = Spec.Gcm.padLen (bytesAt s₀.mem D n).length by rw [lb]; simp only [Spec.Gcm.padLen]; omega,
    show Proof.Gcm.lensBlock al n = Proof.Gcm.lensBlock (bytesAt s₀.mem A al).length (bytesAt s₀.mem D n).length by
      rw [lb, lb]] at L2
  have hg : Spec.Gcm.ghashFrom (ctxH s₀.mem Ctx) 0 ((List.range 8).map fun j =>
      blockAt s₁₁.mem (W + BitVec.ofNat 64 (896 + 16 * j))) =
      Spec.Gcm.ghashFrom (ctxH s₀.mem Ctx) (ghash (ctxH s₀.mem Ctx)
        (blocks (Proof.Gcm.padded (bytesAt s₀.mem A al) (bytesAt s₀.mem D n))))
        [ofBytes (Proof.Gcm.lensBlock (bytesAt s₀.mem A al).length (bytesAt s₀.mem D n).length)] := by
    rw [show ((List.range 8).map fun j => blockAt s₁₁.mem (W + BitVec.ofNat 64 (896 + 16 * j))) =
        Spec.Gcm.blocksAt s₁₁.mem (W + BitVec.ofNat 64 896) 8 by simp only [Spec.Gcm.blocksAt, Offset.add_add],
      Proof.Gcm.blocksAt_eq, L2]
    exact Proof.Gcm.ghash_lead _ _ (by rw [lb]; exact h16)
  -- The tags.
  have bt : ∀ (m : Mem) (p : Addr), bytesAt m p 16 = Spec.Gcm.toBytes (blockAt m p) := fun m p => by
    rw [blockAt, Proof.Cmac.toBytes_ofBytes (lb _ _ _)]
  have hTc : bytesAt s₁₅.mem (W + BitVec.ofNat 64 112) tl =
      (Spec.Gcm.fullTag (ctxCiph s₀.mem Ctx R) (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np 12) (bytesAt s₀.mem A al)
        (bytesAt s₀.mem D n)).take tl := by
    rw [Proof.AesCcm.bytesAt_prefix _ _ htl, bt, tag₁₅, hE, hg, Proof.Gcm.fullTag_eq, hJ0]
  have hTr : bytesAt s₁₅.mem W tl = bytesAt s₀.mem Tg tl := by
    have dT : ∀ {e j : Nat}, 16 ≤ e → e + j ≤ 2560 → (⟨W, tl⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 e, j⟩ :=
      fun h₁ h₂ => Offset.base_disjoint W (by omega) (by omega)
    rw [bytesAt_frame fT₁₅ (one1 (dT (by decide) (by decide))) (by omega),
      bytesAt_frame f₁₄ (one1 (dT (by decide) (by decide))) (by omega), m₁₃, m₁₂,
      bytesAt_frame F₄₁₁ (one1 (dT (by decide) (by decide))) (by omega),
      bytesAt_frame ft₄ (one1 (dT (by decide) (by decide))) (by omega),
      bytesAt_frame h₃.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> exact dT (by decide) (by decide)) (by omega), hT]
  -- The result: 1 exactly when the tags are equal.
  simp only [hTc, hTr] at x10₁₆
  have hb1 : (if ((Spec.Gcm.fullTag (ctxCiph s₀.mem Ctx R) (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np 12) (bytesAt s₀.mem A al) (bytesAt s₀.mem D n)).take tl = bytesAt s₀.mem Tg tl) then 0 else 1) ≤ 1 := by split <;> decide
  refine WP.mono (resBit_ok hb1 s₁₆ x10₁₆) fun s₁₇ ⟨x24₁₇, r₁₇⟩ => ?_
  have he₁₇ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₁₇ := he₁₆.keep (fun r hr => r₁₇.others r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide)) r₁₇.sp r₁₇.rd r₁₇.wr
  have F₁₁₁₇' : Frame [workR W] s₁₁.mem s₁₇.mem := by rw [r₁₇.mem]; exact F₁₁₁₇
  -- What the frames since `t` keep of the saved registers.
  have sv₁₇ : SavedAt s₁₇.mem W s₀ := by
    have h₁ := (o.sv.frame h₃.frame (saved_j0Frame L)).frame ft₄ (one1 (dWW (.inl (by decide)) (by decide) (by decide)))
    have h₂ := (h₁.frame F₄₁₁ (one1 (dWW (.inl (by decide)) (by decide) (by decide))))
    rw [← m₁₂, ← m₁₃] at h₂
    have h₃' := ((h₂.frame f₁₄ (one1 (dWW (.inl (by decide)) (by decide) (by decide)))).frame fT₁₅
      (one1 (dWW (.inr (by decide)) (by decide) (by decide)))).frame fC₁₆ (saved_cmp L)
    rw [r₁₇.mem]; exact h₃'
  have dB : ∀ {e j : Nat}, e + j ≤ 2560 → (880 - 16 * c + n ≤ e ∨ e + j ≤ 880 - 16 * c) →
      (⟨W + BitVec.ofNat 64 (880 - 16 * c), n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 e, j⟩ :=
    fun h₁ h₂ => dWW h₂ (by omega) h₁
  exact ⟨he₁₇, sv₁₇, by rw [r₁₇.rd, rd₁₆, rd₁₅, rd₁₄, rd₁₃, rd₁₂, rd₁₁, rd₁₀, rd₉'],
    by rw [r₁₇.wr, wr₁₆, wr₁₅, wr₁₄, wr₁₃, wr₁₂, wr₁₁, wr₁₀, wr₉'], x24₁₇,
    by rw [r₁₇.others _ (by decide), gk₁₆ .x25 (by simp), k₁₅ .x25 (by simp), x25₆, ← hc],
    by rw [r₁₇.others _ (by decide), gk₁₆ .x26 (by simp), k₁₅ .x26 (by simp), x26₆],
    by rw [r₁₇.others _ (by decide), gk₁₆ .x27 (by simp), k₁₅ .x27 (by simp), x27₆],
    by rw [hc, hJ0, r₁₇.mem, bytesAt_frame fC₁₆ (one1 (dB (by decide) (.inr (by omega)))) (by omega),
      bytesAt_frame fT₁₅ (one1 (dB (by decide) (.inr (by omega)))) (by omega), hPt],
    by rw [bytesAt_frame F₁₁₁₇' (one1 ddW) (by omega), bytesAt_frame Ft₁₁ (one1 ddW) (by omega), hD₀]⟩

/-- `openShortB`, from what `openShortA` leaves. -/
theorem openShortB_ok {Ctx W SP Np A D Tg : Addr} {R al n tl : Nat} {s₀ t u : State}
    (o : OpenIn Ctx W SP Np A D Tg R 12 al n tl s₀ t) (hhi : n ≤ 96) (hok : Spec.Gcm.tagLenOk tl = true)
    (m : ShortMid Ctx W SP Np A D Tg R al n tl s₀ u) :
    WP isa openShortB u (OpenPost Ctx W SP Np A D Tg R 12 al n tl s₀) := by
  have ddW := o.ddW
  have hnlt : n < 2 ^ 64 := o.dat.ok.lt
  have lb := Proof.AesCcm.length_bytesAt
  have selfB : ∀ (m : Mem) (q : Addr) (xs : List Byte) {k : Nat}, xs.length = k → k < 2 ^ 64 →
      bytesAt (writeBytes m q xs) q k = xs := fun m q xs _ hk hk' => by
    subst hk; exact bytesAt_writeBytes_self m q xs hk'
  have wf : ∀ (m : Mem) (q : Addr) (xs : List Byte) {k : Nat}, xs.length = k →
      Frame [⟨q, k⟩] m (writeBytes m q xs) := fun m _ _ _ hk => writeBytes_frame' m hk
  have one1 : ∀ {X r : Region}, X.Disjoint r → ∀ r' ∈ [r], X.Disjoint r' := fun h r' hr' => by
    simp only [List.mem_singleton] at hr'; subst hr'; exact h
  obtain ⟨he₁₇, sv₁₇, rd₁₇, wr₁₇, x24₁₇, x25₁₇, x26₁₇, x27₁₇, pt₁₇, dat₁₇⟩ := m
  simp only [tagEqS] at x24₁₇
  generalize hJ0 : Spec.Gcm.j0 (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np 12) = J at pt₁₇
  generalize hc : (n + 15) / 16 = c at x25₁₇ pt₁₇
  have hc6 : c ≤ 6 := by omega
  have hcn : n ≤ 16 * c := by omega
  have hw : ∀ {v : State}, v.wr = s₀.wr → Covers [⟨W, 2560⟩] v.wr := fun h => by
    rw [h, ← wr₁₇]; exact he₁₇.perm.w
  unfold openShortB
  -- The end, from either branch.
  have fin : ∀ u : State, Env Ctx (W + BitVec.ofNat 64 16) W SP u → SavedAt u.mem W s₀ →
      (((Spec.Gcm.fullTag (ctxCiph s₀.mem Ctx R) (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np 12) (bytesAt s₀.mem A al) (bytesAt s₀.mem D n)).take tl = bytesAt s₀.mem Tg tl) → (u.gpr .x24).setWidth 32 = 1 ∧ bytesAt u.mem D n =
        gctr (ctxCiph s₀.mem Ctx R) (inc32 J) (bytesAt s₀.mem D n)) →
      (¬((Spec.Gcm.fullTag (ctxCiph s₀.mem Ctx R) (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np 12) (bytesAt s₀.mem A al) (bytesAt s₀.mem D n)).take tl = bytesAt s₀.mem Tg tl) → (u.gpr .x24).setWidth 32 = 0 ∧ bytesAt u.mem D n = bytesAt s₀.mem D n) →
      WP isa (.block [mov .x0 .x24]) u (OpenPost Ctx W SP Np A D Tg R 12 al n tl s₀) := by
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
      exact ⟨by rw [x0', a], by rw [r'.mem, b]⟩
  refine WP.seq (WP.ite _ (eval_zero x24₁₇ (by split <;> decide)) (fun hz => WP.block_nil ?_) (fun hz => ?_))
  · -- The tags differ: the text stays as it was.
    have hne : ¬((Spec.Gcm.fullTag (ctxCiph s₀.mem Ctx R) (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np 12) (bytesAt s₀.mem A al) (bytesAt s₀.mem D n)).take tl = bytesAt s₀.mem Tg tl) := fun h => by simp [h] at hz
    exact fin u he₁₇ sv₁₇ (fun h => absurd h hne) fun _ => ⟨by rw [x24₁₇]; simp [hne], dat₁₇⟩
  · -- The tags are equal: the plaintext to the text.
    have heq : ((Spec.Gcm.fullTag (ctxCiph s₀.mem Ctx R) (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np 12) (bytesAt s₀.mem A al) (bytesAt s₀.mem D n)).take tl = bytesAt s₀.mem Tg tl) := by by_contra h; simp [h] at hz
    unfold Impl.AesGcm.AArch64.Stitch.plainOut
    refine WP.seq ?_
    rw [WP.block_append_iff]
    obtain ⟨t₂, run₂, x12t₂, g₂', m₂', _, sp₂', rd₂', wr₂'⟩ := Stitch.atP_ok (c := c) .x12
      Impl.AesGcm.AArch64.Stitch.b1O 1 (by decide) (by unfold Impl.AesGcm.AArch64.Stitch.b1O; omega) u he₁₇.x19
      x25₁₇ (by decide)
    refine WP.of_runBlock ⟨t₂, run₂, ?_⟩
    obtain ⟨s₁₈, run₁₈, x11₁₈, x13₁₈, r₁₈⟩ : ∃ s₁₈, runBlock isa [mov .x11 .x27, mov .x13 .x26] t₂ = some s₁₈ ∧
        s₁₈.gpr .x11 = D ∧ s₁₈.gpr .x13 = BitVec.ofNat 64 n ∧ Regs [.x11, .x13] t₂ s₁₈ := by
      refine ⟨_, by arun [], ?_⟩
      exact ⟨by simp [gpr_write, g₂' .x27 (by decide), x27₁₇], by simp [gpr_write, g₂' .x26 (by decide), x26₁₇],
        ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
    refine WP.of_runBlock ⟨s₁₈, run₁₈, ?_⟩
    have x12₁₈ : s₁₈.gpr .x12 = W + BitVec.ofNat 64 (880 - 16 * c) := by
      rw [r₁₈.others _ (by decide), x12t₂]; rfl
    have rd₁₈ : s₁₈.rd = s₀.rd := by
      rw [r₁₈.rd, rd₂', rd₁₇]
    have wr₁₈ : s₁₈.wr = s₀.wr := by
      rw [r₁₈.wr, wr₂', wr₁₇]
    refine WP.mono (Stitch.copyQ_ok s₁₈ ⟨x12₁₈, x11₁₈, x13₁₈, by omega,
      by rw [rd₁₈, wr₁₈]; exact covers_left (covers_off (hw rfl) (by omega) (by decide)),
      by rw [wr₁₈, ← o.wr₀]; exact o.dat.wr, (ddW.sub_right (Lay.wSub (by omega))).symm⟩)
      fun s₁₉ ⟨m₁₉, g₁₉, sp₁₉, rd₁₉, wr₁₉⟩ => ?_
    have he₁₉ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₁₉ := he₁₇.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> rw [g₁₉ _ (by decide), r₁₈.others _ (by decide), g₂' _ (by decide)])
      (by rw [sp₁₉, r₁₈.sp, sp₂']) (by rw [rd₁₉, r₁₈.rd, rd₂']) (by rw [wr₁₉, r₁₈.wr, wr₂'])
    have m₁₈ : s₁₈.mem = u.mem := by rw [r₁₈.mem, m₂']
    refine fin s₁₉ he₁₉ (by
        rw [m₁₉]
        exact sv₁₇.frame (by rw [← m₁₈]; exact wf _ _ _ (lb _ _ _))
          (one1 (ddW.sub_right (Lay.wSub (by decide))).symm))
      (fun _ => ⟨?_, ?_⟩) fun h => absurd heq h
    · rw [g₁₉ _ (by decide), r₁₈.others _ (by decide), g₂' _ (by decide), x24₁₇]
      simp [heq]
    · rw [m₁₉, selfB _ _ _ (lb _ _ _) (by omega), m₁₈, pt₁₇]

/-- `openShort`, from the state `open` leaves once the received tag is at `W`,
for a record of at most 96 bytes. -/
theorem openShort_post (gh : Gh8Ok) {tb : List Instr} {Ctx W SP Np A D Tg : Addr} {R al n tl : Nat}
    {s₀ t : State} (o : OpenIn Ctx W SP Np A D Tg R 12 al n tl s₀ t)
    (h4 : t.gpr .x4 = A) (h5 : t.gpr .x5 = BitVec.ofNat 64 al) (h6 : t.gpr .x6 = D)
    (h7 : t.gpr .x7 = BitVec.ofNat 64 n) (h16 : al ≤ 16) (hhi : n ≤ 96)
    (hT : bytesAt t.mem W tl = bytesAt s₀.mem Tg tl) (hok : Spec.Gcm.tagLenOk tl = true)
    (htb : ∀ u : State, Env Ctx (W + BitVec.ofNat 64 16) W SP u → u.rd = s₀.rd → u.wr = s₀.wr →
      Frame [workR W, ⟨D, n⟩] s₀.mem u.mem → WP isa (.block tb) u (Stitch.TblPost W (ctxH s₀.mem Ctx) u)) :
    WP isa (Impl.AesGcm.AArch64.Stitch.openShort tb) t (OpenPost Ctx W SP Np A D Tg R 12 al n tl s₀) :=
  (openShort_split tb).symm.wp (WP.seq (WP.mono (openShortA_ok gh o h4 h5 h6 h7 h16 hhi hT hok htb)
    fun _ m => openShortB_ok o hhi hok m))

end VG.Proof.AesGcm.AArch64.Fast
