module

public import VerifiedGarbage.Proof.Gcm.RISCV64.Ghash
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Contract
import VerifiedGarbage.Proof.AesGcm.RISCV64.CryptOk
public import VerifiedGarbage.Proof.AesGcm.RISCV64.TextAbsorb
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Fn
public import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamInit
import VerifiedGarbage.Proof.Gcm.Compose
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Run
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Crypt
public import VerifiedGarbage.Impl.AesGcm.RISCV64

/-!
# AES-GCM on RISC-V: `vg_aes_gcm_stream_encrypt` and `vg_aes_gcm_stream_decrypt`

Untrusted: everything here is checked by Lean. As on ARMv7
(`Proof/AesGcm/Arm/StreamFinish.lean`): the entry saves our caller's
registers and keeps the arguments in `s1`–`s11` (`sc1_wp`); `encrypt` runs
`crypt` on the data and then absorbs what it wrote (`textAbsorb`), `decrypt`
absorbs the data first; both keep `J₀` (`enc_run`, `dec_run`), which is a
state for the text so far followed by the new text (`streamEncrypt_wp`,
`streamDecrypt_wp`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.RISCV64

open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH ctxCiph ghashInput gctr inc32 j0)
open VG.Proof.Gcm (Absorbed Ctr xorKs)

/-- After the entry, from `s₀`. -/
structure SC1 (s₀ s₁ : State) : Prop where
  en : Entered s₀ (s₀.gpr .a7) s₁
  s0 : s₁.gpr .s0 = s₀.gpr .a7
  s1 : s₁.gpr .s1 = s₀.gpr .a2
  s2 : s₁.gpr .s2 = s₀.gpr .a0
  s3 : s₁.gpr .s3 = s₀.gpr .a1
  s11 : s₁.gpr .s11 = s₀.gpr .a4
  s10 : s₁.gpr .s10 = s₀.gpr .a3
  s9 : s₁.gpr .s9 = s₀.gpr .a5
  s8 : s₁.gpr .s8 = s₀.gpr .a6

theorem sc1_wp {s₀ : State} (hW : Covers [⟨s₀.gpr .a7, 2560⟩] s₀.wr) (hal : (s₀.gpr .a7).toNat % 8 = 0) :
    WP isa (.block cryptEntry) s₀ (SC1 s₀) := by
  refine WP.block_append (WP.mono (save_ok (b := .a7) hW hal) fun s₁ ⟨hg, h31, hk, hsv, hf⟩ => ?_)
  obtain e3 : s₁.gpr .a0 = s₀.gpr .a0 := hg _ (by decide)
  obtain e4 : s₁.gpr .a1 = s₀.gpr .a1 := hg _ (by decide)
  obtain e5 : s₁.gpr .a2 = s₀.gpr .a2 := hg _ (by decide)
  obtain e6 : s₁.gpr .a3 = s₀.gpr .a3 := hg _ (by decide)
  obtain e7 : s₁.gpr .a4 = s₀.gpr .a4 := hg _ (by decide)
  obtain e8 : s₁.gpr .a5 = s₀.gpr .a5 := hg _ (by decide)
  obtain e9 : s₁.gpr .a6 = s₀.gpr .a6 := hg _ (by decide)
  crun [Int.reduceNatCast', mov, e3, e4, e5, e6, e7, e8, e9, h31]
  refine ⟨⟨⟨hk.rd, hk.wr, hk.sp⟩, hsv, hf⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp [h31]

/-- `cryptEntry`, then `s7 := t2`. -/
theorem sc1B_wp {s₀ : State} (hW : Covers [⟨s₀.gpr .a7, 2560⟩] s₀.wr) (hal : (s₀.gpr .a7).toNat % 8 = 0) :
    WP isa (.block (cryptEntry ++ [mov .s7 .t2])) s₀ fun s₁ => SC1 s₀ s₁ ∧ s₁.gpr .s7 = s₀.gpr .t2 := by
  simp only [cryptEntry, List.append_assoc, List.cons_append, List.nil_append]
  refine WP.block_append (WP.mono (save_ok (b := .a7) hW hal) fun s₁ ⟨hg, h31, hk, hsv, hf⟩ => ?_)
  obtain e3 : s₁.gpr .a0 = s₀.gpr .a0 := hg _ (by decide)
  obtain e4 : s₁.gpr .a1 = s₀.gpr .a1 := hg _ (by decide)
  obtain e5 : s₁.gpr .a2 = s₀.gpr .a2 := hg _ (by decide)
  obtain e6 : s₁.gpr .a3 = s₀.gpr .a3 := hg _ (by decide)
  obtain e7 : s₁.gpr .a4 = s₀.gpr .a4 := hg _ (by decide)
  obtain e8 : s₁.gpr .a5 = s₀.gpr .a5 := hg _ (by decide)
  obtain e9 : s₁.gpr .a6 = s₀.gpr .a6 := hg _ (by decide)
  obtain e10 : s₁.gpr .t2 = s₀.gpr .t2 := hg _ (by decide)
  crun [Int.reduceNatCast', mov, e3, e4, e5, e6, e7, e8, e9, e10, h31]
  refine ⟨⟨⟨hk.rd, hk.wr, hk.sp⟩, hsv, hf⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp [h31]

/-- The entry, and with the round keys bitsliced `s7 := t2`. -/
theorem entryB_wp {bs : Bool} {s₀ : State} (hW : Covers [⟨s₀.gpr .a7, 2560⟩] s₀.wr)
    (hal : (s₀.gpr .a7).toNat % 8 = 0) :
    WP isa (.block (cryptEntryB bs)) s₀ fun s₁ => SC1 s₀ s₁ ∧ (bs = true → s₁.gpr .s7 = s₀.gpr .t2) := by
  cases bs
  · exact WP.mono (sc1_wp hW hal) fun _ h => ⟨h, Bool.noConfusion⟩
  · exact WP.mono (sc1B_wp hW hal) fun _ h => ⟨h.1, fun _ => h.2⟩

/-- With the round keys bitsliced, `bk = t2` (after `bsPre`): the code may read
it, it is a multiple of 8, apart from the state, `W`, the stack below `sp`
and the data, and holds the round keys of the schedule in the context. -/
structure BsAt (s₀ : State) : Prop where
  rd : Covers [⟨s₀.gpr .t2, 960⟩] s₀.rd
  al : (s₀.gpr .t2).toNat % 8 = 0
  st : (⟨s₀.gpr .t2, 960⟩ : Region).Disjoint ⟨s₀.gpr .a2, 80⟩
  w : (⟨s₀.gpr .t2, 960⟩ : Region).Disjoint ⟨s₀.gpr .a7, 2560⟩
  sk : (⟨s₀.gpr .t2, 960⟩ : Region).Disjoint (below s₀.sp 2048)
  d : (⟨s₀.gpr .t2, 960⟩ : Region).Disjoint ⟨s₀.gpr .a5, (s₀.gpr .a6).toNat⟩
  keys : Proof.Aes.RISCV64.KeysAt s₀.mem (s₀.gpr .t2) (s₀.gpr .a1).toNat
    (bytesAt s₀.mem (s₀.gpr .a0) (16 * ((s₀.gpr .a1).toNat + 1)))

theorem BsAt.saved {s₀ : State} (hb : BsAt s₀) : ∀ r ∈ [savedR (s₀.gpr .a7)], (⟨s₀.gpr .t2, 960⟩ : Region).Disjoint r := by
  intro r hr; simp only [List.mem_singleton] at hr; subst hr
  exact hb.w.sub_right (Lay.wSub (by decide))

theorem BsAt.taFrame {s₀ : State} (hb : BsAt s₀) :
    ∀ r ∈ taFrame (s₀.gpr .a2) (s₀.gpr .a7) s₀.sp, (⟨s₀.gpr .t2, 960⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact hb.st.sub_right (Lay.stSub (by decide))
  · exact hb.st.sub_right (Lay.stSub (by decide))
  · exact hb.w.sub_right (Lay.wSub (by decide))
  · exact hb.w.sub_right (Lay.wSub (by decide))
  · exact hb.sk

section
variable {ex : List Region} {s₀ : State} (h : streamCryptPreX ex s₀)
include h

theorem scLay : Lay (s₀.gpr .a0) (s₀.gpr .a2) (s₀.gpr .a7) := by
  obtain ⟨-, -, dcs, -, dcw, -, dsw, -, fc, fs, -, fw, -, -, a0, a2, a7⟩ := h
  exact Lay.of fc fs fw dcs dcw dsw a0 a2 a7

theorem sc_R : (s₀.gpr .a1).toNat = 10 ∨ (s₀.gpr .a1).toNat = 12 ∨ (s₀.gpr .a1).toNat = 14 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hR, -⟩ := h
  exact hR

theorem sc_al : (s₀.gpr .a7).toNat % 8 = 0 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, a7⟩ := h
  exact a7

theorem sc_stk : StkOk (s₀.gpr .a0) (s₀.gpr .a2) (s₀.gpr .a7) s₀.sp := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hk, -⟩ := h
  exact hk.stk (by simp) (by simp) (by simp)

theorem sc_W : Covers [⟨s₀.gpr .a7, 2560⟩] s₀.wr := by
  rw [h.2.1]; exact covers_mem (by simp)

/-- The environment after the entry. -/
theorem sc_env {s₁ : State} (h1 : SC1 s₀ s₁) : Env s₁.gpr s₀.sp s₁ := by
  obtain hk := sc_stk h
  obtain ⟨hrd, hwr, -⟩ := h
  obtain perm : Perm (s₀.gpr .a0) (s₀.gpr .a2) (s₀.gpr .a7) s₁ :=
    (⟨covers_mem (by rw [hrd]; simp), covers_mem (by rw [hwr]; simp), covers_mem (by rw [hwr]; simp)⟩ :
      Perm (s₀.gpr .a0) (s₀.gpr .a2) (s₀.gpr .a7) s₀).of_eq h1.en.keeps.rd h1.en.keeps.wr
  exact ⟨fun _ _ => rfl, h1.en.keeps.sp, by rw [h1.s2, h1.s1, h1.s0]; exact perm,
    by rw [h1.s2, h1.s1, h1.s0, h1.en.keeps.sp]; exact hk⟩

/-- The data, as `crypt` needs it. -/
theorem sc_dataW {s : State} (hwr' : s.wr = s₀.wr) (hsp : s.sp = s₀.sp) :
    DataW (s₀.gpr .a0) (s₀.gpr .a2) (s₀.gpr .a7) s (s₀.gpr .a5) (s₀.gpr .a6).toNat := by
  obtain ⟨-, hwr, -, dcd, -, dsd, -, ddw, -, -, fd, -, -, hk, -⟩ := h
  obtain hD : Covers [⟨s₀.gpr .a5, (s₀.gpr .a6).toNat⟩] s.wr := by rw [hwr', hwr]; exact covers_mem (by simp)
  exact ⟨⟨covers_left hD, (s₀.gpr .a6).isLt, fd, dsd.symm, ddw, by rw [hsp]; exact hk.buf (by simp)⟩, hD, dcd⟩

end

section
variable {c st w : Addr} (L : Lay c st w)
include L

theorem stp_crFrame {s : State} {D : Addr} {n : Nat} (hd : DataW c st w s D n) {d k : Nat} (h1 : d + k ≤ 48) :
    ∀ r ∈ crFrame st w D n, (⟨st + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (hd.ok.st.sub_right (Lay.stSub (by omega_arith))).symm
  · exact Lay.st_st (.inl h1) (by omega_arith) (by decide)
  · exact L.st_w (by omega_arith) (.inr ⟨by decide, by decide⟩)

theorem stp_taFrame {sp : Addr} (hk : StkOk c st w sp) {d k : Nat} (hd : d + k ≤ 16 ∨ 48 ≤ d ∧ d + k ≤ 80) :
    ∀ r ∈ taFrame st w sp, (⟨st + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact Lay.st_st (by omega_arith) (by omega_arith) (by decide)
  · exact Lay.st_st (by omega_arith) (by omega_arith) (by decide)
  · exact L.st_w (by omega_arith) (.inr ⟨by decide, by decide⟩)
  · exact L.st_w (by omega_arith) (.inr ⟨by decide, by decide⟩)
  · exact hk.st.sub_left (Lay.stSub (by omega_arith))

theorem stp_saved {d k : Nat} (h1 : d + k ≤ 80) :
    ∀ r ∈ [savedR w], (⟨st + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  intro r hr; simp only [List.mem_singleton] at hr; subst hr
  exact L.st_w h1 (.inr ⟨by decide, by decide⟩)

theorem ctx_saved : ∀ r ∈ [savedR w], (⟨c, 256⟩ : Region).Disjoint r := by
  intro r hr; simp only [List.mem_singleton] at hr; subst hr
  exact L.cw'.sub_right (Lay.wSub (by decide))

theorem ctx_taFrame {sp : Addr} (hk : StkOk c st w sp) : ∀ r ∈ taFrame st w sp, (⟨c, 256⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact L.cs.sub_right (Lay.stSub (by decide))
  · exact L.cs.sub_right (Lay.stSub (by decide))
  · exact L.cw'.sub_right (Lay.wSub (by decide))
  · exact L.cw'.sub_right (Lay.wSub (by decide))
  · exact hk.c

omit L in
theorem data_taFrame {s : State} {D : Addr} {n : Nat} (hd : DataOk st w s D n) {sp : Addr} (hsp : s.sp = sp) :
    ∀ r ∈ taFrame st w sp, (⟨D, n⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact hd.st.sub_right (Lay.stSub (by decide))
  · exact hd.st.sub_right (Lay.stSub (by decide))
  · exact hd.w.sub_right (Lay.wSub (by decide))
  · exact hd.w.sub_right (Lay.wSub (by decide))
  · exact hsp ▸ hd.sk

omit L in
theorem data_saved {s : State} {D : Addr} {n : Nat} (hd : DataOk st w s D n) :
    ∀ r ∈ [savedR w], (⟨D, n⟩ : Region).Disjoint r := by
  intro r hr; simp only [List.mem_singleton] at hr; subst hr
  exact hd.w.sub_right (Lay.wSub (by decide))

theorem saved_taFrame {sp : Addr} (hk : StkOk c st w sp) : ∀ r ∈ taFrame st w sp, (savedR w).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact L.saved_st (by decide)
  · exact L.saved_st (by decide)
  · exact saved_w (by decide) (.inl (by decide))
  · exact saved_w (by decide) (.inr (by decide))
  · exact saved_below hk

theorem saved_crFrame {s : State} {D : Addr} {n : Nat} (hd : DataW c st w s D n) :
    ∀ r ∈ crFrame st w D n, (savedR w).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (hd.ok.w.sub_right (Lay.wSub (by decide))).symm
  · exact L.saved_st (by decide)
  · exact saved_w (by decide) (.inr (by decide))

omit L in
/-- `ciphOf` is `ctxCiph`, and a frame apart from the context keeps it. -/
theorem ciph_keep {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (⟨c, 256⟩ : Region).Disjoint r) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) :
    ciphOf m' c R = ctxCiph m c R := ciph_frame hf hd hR

omit L in
theorem ctxH_keep {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (⟨c, 256⟩ : Region).Disjoint r) :
    blockAt m' (c + BitVec.ofNat 64 240) = ctxH m c := by
  rw [ctxH_eq, blockAt_frame hf (fun r hr => (hd r hr).sub_left (Lay.ctxSub (by decide)))]

end

/-- The rounds, as `a1` holds them. -/
abbrev scR (s₀ : State) : Nat := (s₀.gpr .a1).toNat

/-- What `encrypt` (or `decrypt`) does, for the counter block `icb`, the
additional data `a` and the text `ct` so far (only their lengths matter to
the code). -/
structure EncOut (s₀ : State) (icb : Block) (a ct : List Byte) (dec : Bool) (s : State) : Prop where
  ctr : Ctr s₀.mem (s₀.gpr .a2 + BitVec.ofNat 64 48) (s₀.gpr .a2 + BitVec.ofNat 64 64)
      (ctxCiph s₀.mem (s₀.gpr .a0) (scR s₀)) icb ct.length →
    Ctr s.mem (s₀.gpr .a2 + BitVec.ofNat 64 48) (s₀.gpr .a2 + BitVec.ofNat 64 64)
      (ctxCiph s₀.mem (s₀.gpr .a0) (scR s₀)) icb (ct.length + (s₀.gpr .a6).toNat)
  out : Ctr s₀.mem (s₀.gpr .a2 + BitVec.ofNat 64 48) (s₀.gpr .a2 + BitVec.ofNat 64 64)
      (ctxCiph s₀.mem (s₀.gpr .a0) (scR s₀)) icb ct.length →
    bytesAt s.mem (s₀.gpr .a5) (s₀.gpr .a6).toNat =
      xorKs (ctxCiph s₀.mem (s₀.gpr .a0) (scR s₀)) icb ct.length (bytesAt s₀.mem (s₀.gpr .a5) (s₀.gpr .a6).toNat)
  abs : Ctr s₀.mem (s₀.gpr .a2 + BitVec.ofNat 64 48) (s₀.gpr .a2 + BitVec.ofNat 64 64)
      (ctxCiph s₀.mem (s₀.gpr .a0) (scR s₀)) icb ct.length →
    Absorbed s₀.mem (s₀.gpr .a2 + BitVec.ofNat 64 16) (s₀.gpr .a2 + BitVec.ofNat 64 32)
      (ctxH s₀.mem (s₀.gpr .a0)) (ghashInput a ct) →
    Absorbed s.mem (s₀.gpr .a2 + BitVec.ofNat 64 16) (s₀.gpr .a2 + BitVec.ofNat 64 32)
      (ctxH s₀.mem (s₀.gpr .a0))
      (ghashInput a (ct ++ if dec then bytesAt s₀.mem (s₀.gpr .a5) (s₀.gpr .a6).toNat else
        xorKs (ctxCiph s₀.mem (s₀.gpr .a0) (scR s₀)) icb ct.length (bytesAt s₀.mem (s₀.gpr .a5) (s₀.gpr .a6).toNat)))
  j : blockAt s.mem (s₀.gpr .a2) = blockAt s₀.mem (s₀.gpr .a2)

theorem enc_runB [VG.Proof.Gcm.RISCV64.GhashLaw] {bs : Bool} {ex : List Region} {s₀ : State} (h : streamCryptPreX ex s₀)
    (hbs : bs = true → BsAt s₀) (icb : Block) {a ct : List Byte}
    (ha : a.length % 16 = (s₀.gpr .a3).toNat % 16) (hP : (s₀.gpr .a4).toNat = ct.length) :
    WP isa (streamEncryptB bs) s₀ fun s' => abiPreserved s₀ s' ∧ EncOut s₀ icb a ct false s' := by
  obtain L₀ := scLay h
  obtain hR : scR s₀ = 10 ∨ scR s₀ = 12 ∨ scR s₀ = 14 := sc_R h
  obtain hk₀ := sc_stk h
  refine WP.seq (WP.block_append (WP.mono (entryB_wp (bs := bs) (sc_W h) (sc_al h)) fun s₁ ⟨h1, h17⟩ => ?_))
  obtain he₁ := sc_env h h1
  obtain L := L₀.v h1.s2 h1.s1 h1.s0
  refine WP.mono textArgs_ok fun s₂ ⟨h24, h25, h26, hg₂, hk₂⟩ => ?_
  obtain he₂ : Env s₁.gpr s₀.sp s₂ := he₁.keep (fun r hr => hg₂ r (by revert r; decide) (by revert r; decide)
    (by revert r; decide)) hk₂.sp hk₂.rd hk₂.wr
  obtain hd₂₀ := sc_dataW h (s := s₂) (hk₂.wr.trans h1.en.keeps.wr) (hk₂.sp.trans h1.en.keeps.sp)
  obtain hd₂ : DataW (s₁.gpr .s2) (s₁.gpr .s1) (s₁.gpr .s0) s₂ (s₁.gpr .s9) (s₁.gpr .s8).toNat := by
    rw [h1.s2, h1.s1, h1.s0, h1.s9, h1.s8]; exact hd₂₀
  obtain ci : CrIn false s₁.gpr s₀.sp (scR s₀) icb ct.length (s₁.gpr .s9) (s₁.gpr .s9) (s₁.gpr .s8).toNat s₂ :=
    ⟨he₂, h24, by rw [h25, BitVec.ofNat_toNat, BitVec.setWidth_eq], by rw [h26, h1.s11, hP],
      by rw [h1.s3, scR, BitVec.ofNat_toNat, BitVec.setWidth_eq], hR, hd₂, hd₂.ok, rfl, Bool.noConfusion⟩
  obtain f₂ : Frame [savedR (s₀.gpr .a7)] s₀.mem s₂.mem := by rw [hk₂.mem]; exact h1.en.frame
  obtain hbk : bs = true → BkIn (s₁.gpr .s7) (s₁.gpr .s2) (s₁.gpr .s1) (s₁.gpr .s0) s₀.sp (scR s₀) s₂.mem
      (s₁.gpr .s9) (s₁.gpr .s9) (s₁.gpr .s8).toNat s₂ := fun hb => by
    obtain hb₀ := hbs hb
    rw [h17 hb, h1.s2, h1.s1, h1.s0, h1.s9, h1.s8]
    exact ⟨covers_appL (by rw [hk₂.rd, h1.en.keeps.rd]; exact hb₀.rd), hb₀.al, hb₀.st, hb₀.w,
      hb₀.sk, hb₀.d, hb₀.d, keysAt_ctx_frame hR f₂ hb₀.saved (ctx_saved L₀) hb₀.keys⟩
  refine WP.seq (WP.mono (WP.with_rdwr (cryptB_ok L ci hbk)) fun s₃ ⟨co, rd₃, wr₃, sp₃⟩ => ?_)
  obtain hd₃ := hd₂.ok.of_eq rd₃ wr₃ sp₃
  have cf := co.frame
  rw [h1.s1, h1.s0, h1.s9, h1.s8] at cf
  obtain hH₃ : blockAt s₃.mem (s₁.gpr .s2 + BitVec.ofNat 64 240) = ctxH s₀.mem (s₀.gpr .a0) := by
    rw [h1.s2, blockAt_frame cf (fun r hr => (ctx_crFrame L₀ hd₂₀ r hr).sub_left (Lay.ctxSub (by decide))),
      ctxH_keep f₂ (ctx_saved L₀)]
  refine WP.seq (WP.mono (WP.with_rdwr (textAbsorb_ok L (a := a) (ct := ct) co.env hH₃ hd₃ (by rw [h1.s10]; exact ha)
    (by rw [h1.s11]; exact hP))) fun s₄ ⟨ta, rd₄, wr₄, _⟩ => ?_)
  have tf := ta.frame
  rw [h1.s1, h1.s0] at tf
  obtain sv₄ : SavedAt s₄.mem (s₀.gpr .a7) s₀ :=
    (((hk₂.mem ▸ h1.en.saved : SavedAt s₂.mem (s₀.gpr .a7) s₀)).frame cf (saved_crFrame L₀ hd₂₀)).frame tf
      (saved_taFrame L₀ hk₀)
  obtain e31 : s₄.gpr .s0 = s₀.gpr .a7 := (ta.env.fr _ (by decide)).trans h1.s0
  refine WP.mono (restore_ok e31 (sc_al h) (by have := ta.env.perm.w; rw [h1.s0] at this; exact Covers.right this)
    sv₄ ta.env.sp)
    fun s' ⟨ga, hm, _⟩ => ⟨ga, ?_⟩
  obtain hc : ciphOf s₂.mem (s₁.gpr .s2) (scR s₀) = ctxCiph s₀.mem (s₀.gpr .a0) (scR s₀) := by
    rw [h1.s2]; exact ciph_keep f₂ (ctx_saved L₀) hR
  obtain ctr₂ : ∀ {P : Nat}, Ctr s₀.mem (s₀.gpr .a2 + BitVec.ofNat 64 48) (s₀.gpr .a2 + BitVec.ofNat 64 64)
      (ctxCiph s₀.mem (s₀.gpr .a0) (scR s₀)) icb P →
      Ctr s₂.mem (s₁.gpr .s1 + BitVec.ofNat 64 48) (s₁.gpr .s1 + BitVec.ofNat 64 64)
        (ciphOf s₂.mem (s₁.gpr .s2) (scR s₀)) icb P := fun hc₀ => by
    rw [hc, h1.s1]
    exact hc₀.congr (blockAt_frame f₂ (stp_saved L₀ (by decide))) (blockAt_frame f₂ (stp_saved L₀ (by decide)))
  obtain dat₂ : bytesAt s₂.mem (s₀.gpr .a5) (s₀.gpr .a6).toNat = bytesAt s₀.mem (s₀.gpr .a5) (s₀.gpr .a6).toNat :=
    bytesAt_frame f₂ (data_saved hd₂₀.ok) (by have := hd₂₀.ok.lt; omega_arith)
  obtain out₃ : Ctr s₀.mem (s₀.gpr .a2 + BitVec.ofNat 64 48) (s₀.gpr .a2 + BitVec.ofNat 64 64)
      (ctxCiph s₀.mem (s₀.gpr .a0) (scR s₀)) icb ct.length →
      bytesAt s₃.mem (s₀.gpr .a5) (s₀.gpr .a6).toNat =
        xorKs (ctxCiph s₀.mem (s₀.gpr .a0) (scR s₀)) icb ct.length (bytesAt s₀.mem (s₀.gpr .a5) (s₀.gpr .a6).toNat) :=
    fun hc₀ => by
      have := co.out (ctr₂ hc₀)
      rw [hc, h1.s9, h1.s8, dat₂] at this
      exact this
  obtain hd₃₀ : DataOk (s₀.gpr .a2) (s₀.gpr .a7) s₃ (s₀.gpr .a5) (s₀.gpr .a6).toNat := hd₂₀.ok.of_eq rd₃ wr₃ sp₃
  refine ⟨fun hc₀ => ?_, fun hc₀ => ?_, fun hc₀ hab => ?_, ?_⟩
  · rw [hm]
    have := co.ctr (ctr₂ hc₀)
    rw [hc, h1.s1, h1.s8] at this
    exact this.congr (blockAt_frame tf (stp_taFrame L₀ hk₀ (.inr ⟨by decide, by decide⟩)))
      (blockAt_frame tf (stp_taFrame L₀ hk₀ (.inr ⟨by decide, by decide⟩)))
  · rw [hm, bytesAt_frame tf (data_taFrame hd₃₀ (sp₃.trans (hk₂.sp.trans h1.en.keeps.sp))) (by have := hd₃₀.lt; omega_arith)]
    exact out₃ hc₀
  · rw [hm]
    obtain hb := Nat.mod_lt (ghashInput a ct).length (show 16 > 0 by decide)
    obtain hab₃ : Absorbed s₃.mem (s₀.gpr .a2 + BitVec.ofNat 64 16) (s₀.gpr .a2 + BitVec.ofNat 64 32)
        (ctxH s₀.mem (s₀.gpr .a0)) (ghashInput a ct) :=
      (hab.congr (blockAt_frame f₂ (stp_saved L₀ (by decide)))
        (bytesAt_frame f₂ (stp_saved L₀ (by omega_arith)) (by omega_arith))).congr
        (blockAt_frame cf (stp_crFrame L₀ hd₂₀ (by decide)))
        (bytesAt_frame cf (stp_crFrame L₀ hd₂₀ (by omega_arith)) (by omega_arith))
    have := ta.abs (by rw [h1.s1]; exact hab₃)
    rw [h1.s1, h1.s9, h1.s8, out₃ hc₀] at this
    exact this
  · rw [hm, blockAt_frame tf (by simpa using stp_taFrame L₀ hk₀ (d := 0) (k := 16) (.inl (by decide))),
      blockAt_frame cf (by simpa using stp_crFrame L₀ hd₂₀ (d := 0) (k := 16) (by decide)),
      blockAt_frame f₂ (by simpa using stp_saved L₀ (d := 0) (k := 16) (by decide))]

theorem enc_run [VG.Proof.Gcm.RISCV64.GhashLaw] {s₀ : State} (h : streamCryptPre s₀) (icb : Block) {a ct : List Byte}
    (ha : a.length % 16 = (s₀.gpr .a3).toNat % 16) (hP : (s₀.gpr .a4).toNat = ct.length) :
    WP isa streamEncrypt s₀ fun s' => abiPreserved s₀ s' ∧ EncOut s₀ icb a ct false s' :=
  enc_runB (bs := false) h Bool.noConfusion icb ha hP

theorem dec_runB [VG.Proof.Gcm.RISCV64.GhashLaw] {bs : Bool} {ex : List Region} {s₀ : State} (h : streamCryptPreX ex s₀)
    (hbs : bs = true → BsAt s₀) (icb : Block) {a ct : List Byte}
    (ha : a.length % 16 = (s₀.gpr .a3).toNat % 16) (hP : (s₀.gpr .a4).toNat = ct.length) :
    WP isa (streamDecryptB bs) s₀ fun s' => abiPreserved s₀ s' ∧ EncOut s₀ icb a ct true s' := by
  obtain L₀ := scLay h
  obtain hR : scR s₀ = 10 ∨ scR s₀ = 12 ∨ scR s₀ = 14 := sc_R h
  obtain hk₀ := sc_stk h
  refine WP.seq (WP.mono (entryB_wp (bs := bs) (sc_W h) (sc_al h)) fun s₁ ⟨h1, h17⟩ => ?_)
  obtain he₁ := sc_env h h1
  obtain L := L₀.v h1.s2 h1.s1 h1.s0
  have f₁ : Frame [savedR (s₀.gpr .a7)] s₀.mem s₁.mem := h1.en.frame
  obtain hd₁₀ := sc_dataW h (s := s₁) h1.en.keeps.wr h1.en.keeps.sp
  obtain hd₁ : DataOk (s₁.gpr .s1) (s₁.gpr .s0) s₁ (s₁.gpr .s9) (s₁.gpr .s8).toNat := by
    rw [h1.s1, h1.s0, h1.s9, h1.s8]; exact hd₁₀.ok
  obtain hH₁ : blockAt s₁.mem (s₁.gpr .s2 + BitVec.ofNat 64 240) = ctxH s₀.mem (s₀.gpr .a0) := by
    rw [h1.s2]; exact ctxH_keep f₁ (ctx_saved L₀)
  refine WP.seq (WP.mono (WP.with_rdwr (textAbsorb_ok L (a := a) (ct := ct) he₁ hH₁ hd₁
    (by rw [h1.s10]; exact ha) (by rw [h1.s11]; exact hP))) fun s₄ ⟨ta, rd₄, wr₄, sp₄⟩ => ?_)
  have tf := ta.frame
  rw [h1.s1, h1.s0] at tf
  refine WP.seq (WP.mono textArgs_ok fun s₅ ⟨h24, h25, h26, hg₅, hk₅⟩ => ?_)
  obtain he₅ : Env s₁.gpr s₀.sp s₅ := ta.env.keep (fun r hr => hg₅ r (by revert r; decide) (by revert r; decide)
    (by revert r; decide)) hk₅.sp hk₅.rd hk₅.wr
  obtain hd₅₀ := sc_dataW h (s := s₅) (hk₅.wr.trans (wr₄.trans h1.en.keeps.wr))
    (hk₅.sp.trans (sp₄.trans h1.en.keeps.sp))
  obtain hd₅ : DataW (s₁.gpr .s2) (s₁.gpr .s1) (s₁.gpr .s0) s₅ (s₁.gpr .s9) (s₁.gpr .s8).toNat := by
    rw [h1.s2, h1.s1, h1.s0, h1.s9, h1.s8]; exact hd₅₀
  obtain e20 := ta.env.fr .s9 (by decide)
  obtain e19 := ta.env.fr .s8 (by decide)
  obtain e23 := ta.env.fr .s11 (by decide)
  obtain ci : CrIn false s₁.gpr s₀.sp (scR s₀) icb ct.length (s₁.gpr .s9) (s₁.gpr .s9) (s₁.gpr .s8).toNat s₅ :=
    ⟨he₅, by rw [h24, e20], by rw [h25, e19, BitVec.ofNat_toNat, BitVec.setWidth_eq],
      by rw [h26, e23, h1.s11, hP], by rw [h1.s3, scR, BitVec.ofNat_toNat, BitVec.setWidth_eq], hR, hd₅, hd₅.ok,
      rfl, Bool.noConfusion⟩
  obtain hbk : bs = true → BkIn (s₁.gpr .s7) (s₁.gpr .s2) (s₁.gpr .s1) (s₁.gpr .s0) s₀.sp (scR s₀) s₅.mem
      (s₁.gpr .s9) (s₁.gpr .s9) (s₁.gpr .s8).toNat s₅ := fun hb => by
    obtain hb₀ := hbs hb
    rw [h17 hb, h1.s2, h1.s1, h1.s0, h1.s9, h1.s8]
    refine ⟨covers_appL (by rw [hk₅.rd, rd₄, h1.en.keeps.rd]; exact hb₀.rd), hb₀.al, hb₀.st,
      hb₀.w, hb₀.sk, hb₀.d, hb₀.d, ?_⟩
    rw [hk₅.mem]
    exact keysAt_ctx_frame hR tf hb₀.taFrame (ctx_taFrame L₀ hk₀)
      (keysAt_ctx_frame hR f₁ hb₀.saved (ctx_saved L₀) hb₀.keys)
  refine WP.seq (WP.mono (WP.with_rdwr (cryptB_ok L ci hbk)) fun s₆ ⟨co, rd₆, wr₆, _⟩ => ?_)
  have cf := co.frame
  rw [h1.s1, h1.s0, h1.s9, h1.s8] at cf
  obtain sv₆ : SavedAt s₆.mem (s₀.gpr .a7) s₀ :=
    ((h1.en.saved.frame tf (saved_taFrame L₀ hk₀)) : SavedAt s₄.mem (s₀.gpr .a7) s₀) |>.frame
      (hk₅.mem ▸ cf) (saved_crFrame L₀ hd₅₀)
  obtain e31 : s₆.gpr .s0 = s₀.gpr .a7 := (co.env.fr _ (by decide)).trans h1.s0
  refine WP.mono (restore_ok e31 (sc_al h) (by have := co.env.perm.w; rw [h1.s0] at this; exact Covers.right this)
    sv₆ co.env.sp)
    fun s' ⟨ga, hm, _⟩ => ⟨ga, ?_⟩
  obtain hc : ciphOf s₅.mem (s₁.gpr .s2) (scR s₀) = ctxCiph s₀.mem (s₀.gpr .a0) (scR s₀) := by
    rw [h1.s2, hk₅.mem, ciph_frame tf (ctx_taFrame L₀ hk₀) hR]; exact ciph_keep f₁ (ctx_saved L₀) hR
  obtain blk₅ : ∀ {d : Nat}, (d + 16 ≤ 16 ∨ 48 ≤ d ∧ d + 16 ≤ 80) →
      blockAt s₅.mem (s₀.gpr .a2 + BitVec.ofNat 64 d) = blockAt s₀.mem (s₀.gpr .a2 + BitVec.ofNat 64 d) :=
    fun hd => by
      rw [hk₅.mem, blockAt_frame tf (stp_taFrame L₀ hk₀ hd), blockAt_frame f₁ (stp_saved L₀ (by omega_arith))]
  obtain ctr₅ : ∀ {P : Nat}, Ctr s₀.mem (s₀.gpr .a2 + BitVec.ofNat 64 48) (s₀.gpr .a2 + BitVec.ofNat 64 64)
      (ctxCiph s₀.mem (s₀.gpr .a0) (scR s₀)) icb P →
      Ctr s₅.mem (s₁.gpr .s1 + BitVec.ofNat 64 48) (s₁.gpr .s1 + BitVec.ofNat 64 64)
        (ciphOf s₅.mem (s₁.gpr .s2) (scR s₀)) icb P := fun hc₀ => by
    rw [hc, h1.s1]
    exact hc₀.congr (blk₅ (d := 48) (.inr ⟨by decide, by decide⟩)) (blk₅ (d := 64) (.inr ⟨by decide, by decide⟩))
  obtain dat₅ : bytesAt s₅.mem (s₀.gpr .a5) (s₀.gpr .a6).toNat = bytesAt s₀.mem (s₀.gpr .a5) (s₀.gpr .a6).toNat := by
    have hlt := hd₁₀.ok.lt
    rw [hk₅.mem, bytesAt_frame tf (data_taFrame hd₁₀.ok h1.en.keeps.sp) (by omega_arith), bytesAt_frame f₁ (data_saved hd₁₀.ok) (by omega_arith)]
  obtain dat₁ : bytesAt s₁.mem (s₀.gpr .a5) (s₀.gpr .a6).toNat = bytesAt s₀.mem (s₀.gpr .a5) (s₀.gpr .a6).toNat :=
    bytesAt_frame f₁ (data_saved hd₁₀.ok) (by have := hd₁₀.ok.lt; omega_arith)
  refine ⟨fun hc₀ => ?_, fun hc₀ => ?_, fun hc₀ hab => ?_, ?_⟩
  · rw [hm]
    have := co.ctr (ctr₅ hc₀)
    rw [hc, h1.s1, h1.s8] at this
    exact this
  · rw [hm]
    have := co.out (ctr₅ hc₀)
    rw [hc, h1.s9, h1.s8, dat₅] at this
    exact this
  · simp only [hm, ↓reduceIte]
    obtain hab₁ : Absorbed s₁.mem (s₀.gpr .a2 + BitVec.ofNat 64 16) (s₀.gpr .a2 + BitVec.ofNat 64 32)
        (ctxH s₀.mem (s₀.gpr .a0)) (ghashInput a ct) :=
      hab.congr (blockAt_frame f₁ (stp_saved L₀ (by decide)))
        (bytesAt_frame f₁ (stp_saved L₀ (by omega_arith)) (by omega_arith))
    have := ta.abs (by rw [h1.s1]; exact hab₁)
    rw [h1.s1, h1.s9, h1.s8, dat₁] at this
    rw [← hk₅.mem] at this
    exact this.congr (blockAt_frame cf (stp_crFrame L₀ hd₅₀ (by decide)))
      (bytesAt_frame cf (stp_crFrame L₀ hd₅₀ (by omega_arith)) (by omega_arith))
  · rw [hm, blockAt_frame cf (by simpa using stp_crFrame L₀ hd₅₀ (d := 0) (k := 16) (by decide))]
    simpa using blk₅ (d := 0) (.inl (by decide))

theorem dec_run [VG.Proof.Gcm.RISCV64.GhashLaw] {s₀ : State} (h : streamCryptPre s₀) (icb : Block) {a ct : List Byte}
    (ha : a.length % 16 = (s₀.gpr .a3).toNat % 16) (hP : (s₀.gpr .a4).toNat = ct.length) :
    WP isa streamDecrypt s₀ fun s' => abiPreserved s₀ s' ∧ EncOut s₀ icb a ct true s' :=
  dec_runB (bs := false) h Bool.noConfusion icb ha hP

theorem streamEncryptB_wp [VG.Proof.Gcm.RISCV64.GhashLaw] {bs : Bool} {ex : List Region} {s₀ : State}
    (h' : streamCryptPreX ex s₀) (hbs : bs = true → BsAt s₀) :
    WP isa (streamEncryptB bs) s₀ fun s' => abiPreserved s₀ s' ∧ streamEncryptRISCV64.post s₀ s' := by
  obtain h₀ := enc_runB h' hbs 0 (a := List.replicate ((s₀.gpr .a3).toNat % 16) 0)
    (ct := List.replicate (s₀.gpr .a4).toNat 0) (by simp) (by simp)
  refine WP.mono (WP.forall_det (WP.mono h₀ fun _ hh => hh.1)
    (P := fun i : List Byte × List Byte × List Byte =>
      let ciph := ctxCiph s₀.mem (s₀.gpr .a0) (s₀.gpr .a1).toNat
      let hh := ctxH s₀.mem (s₀.gpr .a0)
      StreamRepr s₀.mem (s₀.gpr .a2) ciph hh i.1 i.2.1 (gctr ciph (inc32 (j0 hh i.1)) i.2.2) ∧
        s₀.gpr .a3 = BitVec.ofNat 64 i.2.1.length ∧ (s₀.gpr .a4).toNat = i.2.2.length)
    fun i hi => enc_runB h' hbs (inc32 (j0 (ctxH s₀.mem (s₀.gpr .a0)) i.1)) (a := i.2.1)
      (ct := gctr (ctxCiph s₀.mem (s₀.gpr .a0) (s₀.gpr .a1).toNat) (inc32 (j0 (ctxH s₀.mem (s₀.gpr .a0)) i.1)) i.2.2)
      (by rw [hi.2.1, toNat_mod16]) (by rw [Proof.Gcm.length_gctr]; exact hi.2.2))
    fun s' hh => ⟨hh.1, fun iv a p hs hl hp => ?_⟩
  obtain ⟨-, eo⟩ := hh.2 ⟨iv, a, p⟩ ⟨hs, hl, hp⟩
  rw [Proof.Gcm.streamRepr_iff] at hs
  obtain ⟨hj, hab, hct⟩ := hs
  obtain hl' : (gctr (ctxCiph s₀.mem (s₀.gpr .a0) (s₀.gpr .a1).toNat)
      (inc32 (j0 (ctxH s₀.mem (s₀.gpr .a0)) iv)) p).length = p.length := Proof.Gcm.length_gctr _ _ _
  obtain eo₁ := eo.ctr hct
  obtain eo₂ := eo.out hct
  obtain eo₃ := eo.abs hct hab
  simp only [Bool.false_eq_true, ite_false] at eo₃
  rw [hl'] at eo₁ eo₂ eo₃
  rw [← Proof.Gcm.gctr_append] at eo₃
  refine ⟨?_, ?_⟩
  · rw [Proof.Gcm.streamRepr_iff]
    refine ⟨eo.j.trans hj, eo₃, ?_⟩
    rw [Proof.Gcm.length_gctr, List.length_append, length_bytesAt]; exact eo₁
  · rw [eo₂, Proof.Gcm.gctr_append, List.drop_left' hl']

theorem streamEncrypt_wp [VG.Proof.Gcm.RISCV64.GhashLaw] {s₀ : State} (h : streamEncryptRISCV64.pre s₀) :
    WP isa streamEncrypt s₀ fun s' => abiPreserved s₀ s' ∧ streamEncryptRISCV64.post s₀ s' :=
  streamEncryptB_wp (bs := false) (ex := []) h Bool.noConfusion

theorem streamDecryptB_wp [VG.Proof.Gcm.RISCV64.GhashLaw] {bs : Bool} {ex : List Region} {s₀ : State}
    (h' : streamCryptPreX ex s₀) (hbs : bs = true → BsAt s₀) :
    WP isa (streamDecryptB bs) s₀ fun s' => abiPreserved s₀ s' ∧ streamDecryptRISCV64.post s₀ s' := by
  obtain h₀ := dec_runB h' hbs 0 (a := List.replicate ((s₀.gpr .a3).toNat % 16) 0)
    (ct := List.replicate (s₀.gpr .a4).toNat 0) (by simp) (by simp)
  refine WP.mono (WP.forall_det (WP.mono h₀ fun _ hh => hh.1)
    (P := fun i : List Byte × List Byte × List Byte =>
      let ciph := ctxCiph s₀.mem (s₀.gpr .a0) (s₀.gpr .a1).toNat
      let hh := ctxH s₀.mem (s₀.gpr .a0)
      StreamRepr s₀.mem (s₀.gpr .a2) ciph hh i.1 i.2.1 i.2.2 ∧
        s₀.gpr .a3 = BitVec.ofNat 64 i.2.1.length ∧ (s₀.gpr .a4).toNat = i.2.2.length)
    fun i hi => dec_runB h' hbs (inc32 (j0 (ctxH s₀.mem (s₀.gpr .a0)) i.1)) (a := i.2.1) (ct := i.2.2)
      (by rw [hi.2.1, toNat_mod16]) hi.2.2)
    fun s' hh => ⟨hh.1, fun iv a c hs hl hp => ?_⟩
  obtain ⟨-, eo⟩ := hh.2 ⟨iv, a, c⟩ ⟨hs, hl, hp⟩
  rw [Proof.Gcm.streamRepr_iff] at hs
  obtain ⟨hj, hab, hct⟩ := hs
  obtain eo₁ := eo.ctr hct
  obtain eo₂ := eo.out hct
  obtain eo₃ := eo.abs hct hab
  simp only [ite_true] at eo₃
  refine ⟨?_, ?_⟩
  · rw [Proof.Gcm.streamRepr_iff]
    refine ⟨eo.j.trans hj, eo₃, ?_⟩
    rw [List.length_append, length_bytesAt]; exact eo₁
  · rw [eo₂, Proof.Gcm.gctr_append, List.drop_left' (Proof.Gcm.length_gctr _ _ _)]

theorem streamDecrypt_wp [VG.Proof.Gcm.RISCV64.GhashLaw] {s₀ : State} (h : streamDecryptRISCV64.pre s₀) :
    WP isa streamDecrypt s₀ fun s' => abiPreserved s₀ s' ∧ streamDecryptRISCV64.post s₀ s' :=
  streamDecryptB_wp (bs := false) (ex := []) h Bool.noConfusion

end VG.Proof.AesGcm.RISCV64
