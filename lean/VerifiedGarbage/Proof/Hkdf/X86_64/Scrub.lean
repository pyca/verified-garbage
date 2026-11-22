module

public import VerifiedGarbage.Proof.Hkdf.X86_64.Table
public import VerifiedGarbage.Proof.Hkdf.Common
public import VerifiedGarbage.Proof.HmacTable.X86_64.Up
public import VerifiedGarbage.Proof.Framework.X86_64.TableFill
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Impl.Hkdf.X86_64.Fn
public import VerifiedGarbage.Proof.Variants.MdHash.X86_64
import VerifiedGarbage.Proof.Framework.X86_64.ScrubProved
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Sha256.Stream
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.Hkdf.X86_64.Fn
meta import VerifiedGarbage.Proof.Framework.X86_64.TableFill

/-!
# HKDF on x86-64, without secret residue

Each function, generic over the HMAC implementations its table holds, which
it calls indirectly, followed by its cleanup (`Impl.Hkdf.X86_64.Fn`), returns
with the caller-saved registers cleared and the stack its contract gives it
zeroed. It clears at the level `sse`, of the baseline ISA, which the AVX
code it may run through the table needs no more of than that its upper
halves agree after it (`X86_64.Scrub.verifiedScrubbedAllUpFill`). What the
cleanup needs of the code is evaluated once, with a stub in the place of
HMAC's functions (`stubFns`); the code with the functions of every variant
in their place is that code filled (`key_tfill`), from what is evaluated of
each variant's functions once (`HmacTable.X86_64.variants_up`). The
postconditions read the memory on return only within the buffers they write
(`keyOut`): `key`'s, through the streaming states' `Repr`, which depends on
their bytes alone (`Proof.Hkdf.streamingOf_local`).
-/

@[expose] public section

namespace VG.Proof.Hkdf.X86_64.Scrub

open VG.X86_64 VG.X86_64.Scrub
open VG.Impl.Mgf1.X86_64.Table (Fns)
open VG.Proof.Pbkdf2.Md.X86_64 (MdHash)
open VG.Proof.HmacTable.X86_64 (HmacUp tables fnsOf names mem_names)

/-- A stub in the place of each of HMAC's functions. -/
def stubFns : Fns := ⟨[("t", tableStub 24)], [("t", tableStub 24)], [("t", tableStub 24)]⟩

theorem mem_tableFns {vs : List MdHash} {f : String} (h : f ∈ names vs) :
    f ∈ tableFns [("hmac", tables vs)] := by
  simp only [tableFns, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_flatMap]
  simp only [names, List.mem_flatten, List.mem_map] at h
  obtain ⟨_, ⟨t, ht, rfl⟩, hf⟩ := h
  exact ⟨t, ht, hf⟩

/-- What the cleanup needs of each of the functions the tables of `vs` hold
in each word. -/
theorem fnsOf_up {vs : List MdHash} (hv : ∀ w ∈ vs, HmacUp w) :
    (∀ q ∈ (fnsOf vs).init, upCallee q.2 24 = true ∧ q.1 ∈ names vs) ∧
      (∀ q ∈ (fnsOf vs).upd, upCallee q.2 24 = true ∧ q.1 ∈ names vs) ∧
      (∀ q ∈ (fnsOf vs).fin, upCallee q.2 24 = true ∧ q.1 ∈ names vs) := by
  refine ⟨?_, ?_, ?_⟩ <;> intro q hq <;> obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hq
  · exact ⟨(hv w hw).1, (mem_names hw).1⟩
  · exact ⟨(hv w hw).2.1, (mem_names hw).2.1⟩
  · exact ⟨(hv w hw).2.2, (mem_names hw).2.2⟩

/-- No instruction of an indirect call by `i` of `ts` writes `rsp` if `i`
does not and none of `ts`' do. -/
theorem icalls_sp (i : Instr) (hi : (!isa.writesSp i) = true) :
    ∀ ts : List (String × Prog isa), (∀ q ∈ ts, q.2.all (fun i => !isa.writesSp i) = true) →
      (Code.icalls i ts).all (fun i => !isa.writesSp i) = true
  | [], _ => rfl
  | q :: ts, h => by
    rw [Code.icalls, Code.all, hi, h q (List.mem_cons_self ..),
      icalls_sp i hi ts fun r hr => h r (List.mem_cons_of_mem _ hr)]
    rfl

theorem init_sp (vs : List MdHash) :
    ∀ q ∈ (fnsOf vs).init, q.2.all (fun i => !isa.writesSp i) = true := by
  intro q hq; obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hq
  exact w.hmacAnySp

/-- Code that never writes `rsp` writes it only in its frames. -/
theorem noSp_all {c : Prog isa} (h : NoSp c) : c.all (fun i => !isa.writesSp i) = true :=
  Code.all_of_allInstrs (by
    rw [Code.allInstrs_eq]
    exact List.all_eq_true.mpr fun i hi => by
      have := h i hi
      cases i <;> simp_all [Taint.clobbers, Taint.dstOf, isa, Instr.dst]
      exact ⟨fun e => this.1 e.symm, fun e => this.2 e.symm⟩)

theorem upd_sp (vs : List MdHash) : ∀ q ∈ (fnsOf vs).upd, q.2.all (fun i => !isa.writesSp i) = true := by
  intro q hq; obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hq
  exact noSp_all w.ok.updSp

theorem fin_sp (vs : List MdHash) : ∀ q ∈ (fnsOf vs).fin, q.2.all (fun i => !isa.writesSp i) = true := by
  intro q hq; obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hq
  exact noSp_all (Proof.Hkdf.X86_64.Extract.hFsp w)

/-! ## `vg_hkdf_key` -/

/-- `key`'s postcondition reads the memory on return only within `key`. -/
theorem keyOut (vs : List MdHash) :
    PostOut (Proof.Hkdf.X86_64.specKey vs) (Spec.Hkdf.keySig.retBits 64) :=
  postOut_of_local (ScrubAbi.plain.tables _ _) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [prk, pl, key, hm], _ =>
      simp only [Spec.Hkdf.keySig, Sig.bufs, List.mem_cons, forall_eq_or_imp, Elem.size, Nat.mul_one] at hb
      intro H S hH hSt
      have hl : Proof.Hmac.ReprLocal S := Proof.Hkdf.streamingOf_local hSt
      have hS := Spec.Hkdf.streamingOf_stateBytes H S hSt
      obtain ⟨hi, ho⟩ := h H S hH hSt
      have keep : ∀ o, o + S.stateBytes ≤ 384 → ∀ i < S.stateBytes,
          m₂ (key + BitVec.ofNat 64 o + BitVec.ofNat 64 i) = m₁ (key + BitVec.ofNat 64 o + BitVec.ofNat 64 i) :=
        fun o ho i hi => (hb.2.1 _ (by
          rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
          exact Offset.contains_base _ (by omega_using [ho, hi]) (by omega_using [ho, hi]))).symm
      have k0 := keep 0 (by omega_using [hS])
      rw [BitVec.add_zero] at k0
      exact ⟨hl k0 hi, hl (keep 192 (by omega_using [hS])) ho⟩

theorem key_tfill {vs : List MdHash} (hv : ∀ w ∈ vs, HmacUp w) :
    TFill 24 (names vs) (Impl.Hkdf.X86_64.key stubFns) (Impl.Hkdf.X86_64.key (fnsOf vs)) := by
  have hI := (fnsOf_up hv).1
  unfold Impl.Hkdf.X86_64.key Impl.Hkdf.X86_64.keyMain
  tfill_calls

theorem key_sp (vs : List MdHash) :
    (Impl.Hkdf.X86_64.key (fnsOf vs)).all (fun i => !isa.writesSp i) = true := by
  rw [Impl.Hkdf.X86_64.key, Impl.Hkdf.X86_64.keyMain, Code.all, Code.all, icalls_sp _ rfl _ (init_sp vs)]
  rfl

/-- `vg_hkdf_key` as emitted, cleanup included (`Impl.Hkdf.X86_64.Fn.key`),
with the tables of `vs`: it meets its contract in constant time and returns
without secret residue. -/
theorem key_scrubbed {vs : List MdHash} (hO : OK vs) (hS : Streams vs) (hv : ∀ w ∈ vs, HmacUp w) :
    VerifiedScrubbed target (Impl.Hkdf.X86_64.Fn.key (fnsOf vs)) (Proof.Hkdf.X86_64.specKey vs) 0 :=
  verifiedScrubbedAllUpFill (api := Spec.Hkdf.keyApi)
    { tables := [("hmac", tables vs)]
      code := Impl.Hkdf.X86_64.key (fnsOf vs)
      contract := Proof.Hkdf.X86_64.specKey vs
      verified := Proof.Hkdf.X86_64.key_spec hO hS
      spSafe := key_sp vs }
    (keyOut vs) (key_tfill hv) (fun _ h => mem_tableFns h)

theorem key_spSafe (vs : List MdHash) :
    (Impl.Hkdf.X86_64.Fn.key (fnsOf vs)).all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (key_sp vs)

/-! ## `vg_hkdf_extract` -/

/-- `extract`'s postcondition reads the memory on return only within `prk`
(of `prk_len` bytes, the digest length, by the precondition). -/
theorem extractOut (vs : List MdHash) :
    PostOut (Proof.Hkdf.X86_64.specExtract vs) (Spec.Hkdf.extractSig.retBits 64) :=
  postOut_of_local_pre (ScrubAbi.plain.tables _ _) fun vs m m₁ m₂ r hlen hpre hb h => by
    match vs, hlen with
    | [salt, sl, ikm, il, prk, pl, hm], _ =>
      simp only [Spec.Hkdf.extractSig, Sig.bufs, List.mem_cons, forall_eq_or_imp, Elem.size, Nat.mul_one] at hb
      intro H F hH hF
      obtain ⟨hpl, -⟩ := hpre H hH
      have := h H F hH hF
      refine (Proof.Sha256.Stream.bytesAt_congr fun i hi => (hb.2.2.1 _ ?_).symm).trans this
      have hpl' : pl.toNat = H.len := hpl
      exact Offset.contains_base _ (by omega_using [hpl', hi]) (by
        have := pl.isLt; omega_using [hpl', hi, this])

theorem extract_tfill {vs : List MdHash} (hv : ∀ w ∈ vs, HmacUp w) :
    TFill 24 (names vs) (Impl.Hkdf.X86_64.extract stubFns) (Impl.Hkdf.X86_64.extract (fnsOf vs)) := by
  have hI := (fnsOf_up hv).1
  have hU := (fnsOf_up hv).2.1
  have hF := (fnsOf_up hv).2.2
  unfold Impl.Hkdf.X86_64.extract Impl.Hkdf.X86_64.extractMain Impl.Mgf1.X86_64.seqs Impl.Hkdf.X86_64.tcall
  tfill_calls

theorem extract_sp (vs : List MdHash) :
    (Impl.Hkdf.X86_64.extract (fnsOf vs)).all (fun i => !isa.writesSp i) = true := by
  have h0 := icalls_sp (.callr .r11) rfl _ (init_sp vs)
  have h1 := icalls_sp (.callr .r11) rfl _ (upd_sp vs)
  have h2 := icalls_sp (.callr .r11) rfl _ (fin_sp vs)
  simp only [] at h0 h1 h2
  simp only [Impl.Hkdf.X86_64.extract, Impl.Hkdf.X86_64.extractMain, Impl.Mgf1.X86_64.seqs,
    Impl.Hkdf.X86_64.tcall, Code.all, h0, h1, h2, Bool.and_true]
  rfl

/-- `vg_hkdf_extract` as emitted, cleanup included (`Impl.Hkdf.X86_64.Fn.extract`),
with the tables of `vs`: it meets its contract in constant time and returns
without secret residue. -/
theorem extract_scrubbed {vs : List MdHash} (hO : OK vs) (hS : Streams vs) (hv : ∀ w ∈ vs, HmacUp w) :
    VerifiedScrubbed target (Impl.Hkdf.X86_64.Fn.extract (fnsOf vs)) (Proof.Hkdf.X86_64.specExtract vs) 0 :=
  verifiedScrubbedAllUpFill (api := Spec.Hkdf.extractApi)
    { tables := [("hmac", tables vs)]
      code := Impl.Hkdf.X86_64.extract (fnsOf vs)
      contract := Proof.Hkdf.X86_64.specExtract vs
      verified := Proof.Hkdf.X86_64.extract_spec hO hS
      spSafe := extract_sp vs }
    (extractOut vs) (extract_tfill hv) (fun _ h => mem_tableFns h)

theorem extract_spSafe (vs : List MdHash) :
    (Impl.Hkdf.X86_64.Fn.extract (fnsOf vs)).all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (extract_sp vs)

/-! ## `vg_hkdf_expand` -/

/-- `expand`'s postcondition reads the memory on return only within `out`. -/
theorem expandOut (vs : List MdHash) :
    PostOut (Proof.Hkdf.X86_64.specExpand vs) (Spec.Hkdf.expandSig.retBits 64) :=
  postOut_of_local (ScrubAbi.plain.tables _ _) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [key, info, il, out, ol, hm], _ =>
      simp only [Spec.Hkdf.expandSig, Sig.bufs, List.mem_cons, forall_eq_or_imp, Elem.size, Nat.mul_one] at hb
      intro H S prk hH hSt hK
      rw [h H S prk hH hSt hK]
      exact congrArg some (Proof.Sha256.Stream.bytesAt_congr fun i hi => by
        have hi' : i < ol.toNat := hi
        exact hb.2.2.1 _ (Offset.contains_base _ (by omega_using [hi']) (by have := ol.isLt; omega_using [hi', this])))

theorem expand_tfill {vs : List MdHash} (hv : ∀ w ∈ vs, HmacUp w) :
    TFill 24 (names vs) (Impl.Hkdf.X86_64.expand stubFns) (Impl.Hkdf.X86_64.expand (fnsOf vs)) := by
  have hU := (fnsOf_up hv).2.1
  have hF := (fnsOf_up hv).2.2
  unfold Impl.Hkdf.X86_64.expand Impl.Hkdf.X86_64.expandMain Impl.Mgf1.X86_64.seqs Impl.Hkdf.X86_64.block
    Impl.Hkdf.X86_64.tcall
  tfill_calls

theorem expand_sp (vs : List MdHash) :
    (Impl.Hkdf.X86_64.expand (fnsOf vs)).all (fun i => !isa.writesSp i) = true := by
  have h1 := icalls_sp (.callr .r11) rfl _ (upd_sp vs)
  have h2 := icalls_sp (.callr .r11) rfl _ (fin_sp vs)
  simp only [] at h1 h2
  simp only [Impl.Hkdf.X86_64.expand, Impl.Hkdf.X86_64.expandMain, Impl.Mgf1.X86_64.seqs, Impl.Hkdf.X86_64.block,
    Impl.Hkdf.X86_64.outLen, Impl.Hkdf.X86_64.outCopy, Impl.Mgf1.X86_64.byteLoop,
    Impl.Hkdf.X86_64.tcall, Code.all, h1, h2, Bool.and_true]
  rfl

/-- `vg_hkdf_expand` as emitted, cleanup included (`Impl.Hkdf.X86_64.Fn.expand`),
with the tables of `vs`: it meets its contract in constant time and returns
without secret residue. -/
theorem expand_scrubbed {vs : List MdHash} (hO : OK vs) (hS : Streams vs) (hv : ∀ w ∈ vs, HmacUp w) :
    VerifiedScrubbed target (Impl.Hkdf.X86_64.Fn.expand (fnsOf vs)) (Proof.Hkdf.X86_64.specExpand vs) 0 :=
  verifiedScrubbedAllUpFill (api := Spec.Hkdf.expandApi)
    { tables := [("hmac", tables vs)]
      code := Impl.Hkdf.X86_64.expand (fnsOf vs)
      contract := Proof.Hkdf.X86_64.specExpand vs
      verified := Proof.Hkdf.X86_64.expand_spec hO hS
      spSafe := expand_sp vs }
    (expandOut vs) (expand_tfill hv) (fun _ h => mem_tableFns h)

theorem expand_spSafe (vs : List MdHash) :
    (Impl.Hkdf.X86_64.Fn.expand (fnsOf vs)).all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (expand_sp vs)

/-! ## The registrations' variants -/

open VG.Proof.Variants.MdHash.X86_64 (variants)

/-- Each variant's streaming states are the specification's. -/
theorem variants_streams : Streams variants := by
  intro w hw
  simp only [variants, Proof.Variants.MdHash.X86_64.md5Variants, Proof.Variants.MdHash.X86_64.sha1Variants,
    Proof.Variants.MdHash.X86_64.sha224Variants, Proof.Variants.MdHash.X86_64.sha256Variants,
    Proof.Variants.MdHash.X86_64.sha384Variants, Proof.Variants.MdHash.X86_64.sha512Variants,
    Proof.Variants.MdHash.X86_64.sha512_224Variants, Proof.Variants.MdHash.X86_64.sha512_256Variants,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hw
  repeat' (rcases hw with rfl | hw)
  all_goals rfl

/-- `vg_hkdf_key` as emitted, with the tables of the registrations' variants,
given what the registration checks of them (`OK`). -/
theorem key_scrubbedV (hO : OK variants) :
    VerifiedScrubbed target (Impl.Hkdf.X86_64.Fn.key (fnsOf variants)) (Proof.Hkdf.X86_64.specKey variants) 0 :=
  key_scrubbed hO variants_streams Proof.HmacTable.X86_64.variants_up

/-- `vg_hkdf_extract` as emitted, with the tables of the registrations'
variants. -/
theorem extract_scrubbedV (hO : OK variants) :
    VerifiedScrubbed target (Impl.Hkdf.X86_64.Fn.extract (fnsOf variants)) (Proof.Hkdf.X86_64.specExtract variants) 0 :=
  extract_scrubbed hO variants_streams Proof.HmacTable.X86_64.variants_up

/-- `vg_hkdf_expand` as emitted, with the tables of the registrations'
variants. -/
theorem expand_scrubbedV (hO : OK variants) :
    VerifiedScrubbed target (Impl.Hkdf.X86_64.Fn.expand (fnsOf variants)) (Proof.Hkdf.X86_64.specExpand variants) 0 :=
  expand_scrubbed hO variants_streams Proof.HmacTable.X86_64.variants_up

end VG.Proof.Hkdf.X86_64.Scrub
