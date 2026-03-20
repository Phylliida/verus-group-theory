Plan: Proving Higman's Embedding Theorem for CEERs                           
│
│                                                                              
│
│ Context                                                                      
│
│                                                                              
│
│ The last external_body axiom in verus-computability-theory is                
│
│ axiom_ceer_embeds_in_fp_group in src/ceer_benign.rs (line 66). It 
asserts:   │
│ given ceer_wf(e), there exists a finitely presented group with a 
faithful    │
│ embedding of the CEER equivalence structure. Removing it completes the       
│
│ formal verification chain from ZFC equivalence to finitely presented 
groups, │
│  leaving only the Church-Turing thesis 
(axiom_enumerator_machine_exists) as  │
│ trusted assumption.                                                          
│
│                                                                              
│
│ Research Background & Sources                                                
│
│                                                                              
│
│ Three approaches were evaluated:                                             
│
│                                                                              
│
│ Approach A: Higman Operations (abstract). Higman's original 1961 proof 
uses  │
│ 9 abstract operations on recursively enumerable sets, showing each 
preserves │
│  "benignness." Too abstract for our concrete machine infrastructure; 
doesn't │
│  leverage HNN/Britton.                                                       
│
│                                                                              
│
│ Approach B: Direct Aanderaa-Cohen machine encoding. Aanderaa (1976) and      
│
│ Cohen (1980) encode computations directly as group relations via 
"modular    │
│ machines" — machines operating on pairs (alpha, beta) via modular 
arithmetic │
│  with unconditional transitions. Produces a f.p. group directly but 
can't    │
│ leverage the already-proved lemma_rope_trick.                                
│
│                                                                              
│
│ Approach C (chosen): Machine encoding for benignness + Rope Trick. 
Hybrid    │
│ approach that:                                                               
│
│ 1. Uses Aanderaa-Cohen modular machines to encode computation as HNN         
│
│ relations                                                                    
│
│ 2. Builds a benign witness (which the Rope Trick consumes)                   
│
│ 3. Leverages existing infrastructure: HNN extensions, Britton's lemma,       
│
│ lemma_rope_trick                                                             
│
│                                                                              
│
│ Key references:                                                              
│
│ - Mikaelian 2025, "An explicit algorithm for the Higman Embedding 
Theorem"   │
│ (arXiv:2507.04347) — 8-step constructive algorithm                           
│
│ - Mikaelian 2019, "A modified proof for Higman's embedding theorem"          
│
│ (arXiv:1908.10153) — cleaner proof via modular machines                      
│
│ - Aanderaa 1976 — modular machines avoid zero-test encoding problem          
│
│ - Lyndon & Schupp, "Combinatorial Group Theory" Ch. IV — standard 
reference  │
│ for HNN/Britton/Higman                                                       
│
│                                                                              
│
│ Why modular machines? Counter machines (our RegisterMachine) use 
DecJump     │
│ which is a conditional zero-test — this cannot be directly encoded as 
an     │
│ unconditional HNN conjugation relation. Modular machines replace 
zero-test   │
│ with modular residue checks (unconditional: check alpha mod m, always 
do     │
│ something), making each transition encodable as a single HNN 
association.    │
│                                                                              
│
│ Universal word collapse warning: The encoding universal_word(n) = 
y^{-n} x   │
│ y^n in F_2 has a pitfall: if universal_word(0) ≡ universal_word(1) in 
any    │
│ quotient, conjugation by y forces ALL universal words equivalent. This 
is    │
│ already documented in ceer_benign.rs lines 20-31. The construction must      
│
│ avoid this — the machine group encoding naturally avoids it because 
distinct │
│  computations produce distinct config words (faithfulness via Britton).      
│
│                                                                              
│
│ Existing Infrastructure                                                      
│
│                                                                              
│
│ verus-group-theory (558 fns):                                                
│
│ - hnn.rs: HNNData, hnn_presentation, lemma_hnn_conjugation,                  
│
│ lemma_base_embeds_in_hnn                                                     
│
│ - britton.rs/britton_proof.rs (12K lines): axiom_britton_lemma,              
│
│ lemma_hnn_injective (98% proved, 3 assume(false))                            
│
│ - benign.rs: BenignWitness with 10 validity clauses, is_benign,              
│
│ in_generated_subgroup                                                        
│
│ - higman_operations.rs: lemma_rope_trick — PROVED. Takes                     
│
│ benign_witness_valid(free_group(2), gens, witness), produces f.p.            
│
│ presentation + faithful 2-word embedding                                     
│
│ - amalgamated_free_product.rs: AmalgamatedData, left/right embedding 
lemmas  │
│ - free_product.rs: free_product, shift_word, embedding lemmas                
│
│ - quotient.rs: add_relators, preservation/identity lemmas                    
│
│                                                                              
│
│ verus-computability-theory (204 fns):                                        
│
│ - machine.rs: RegisterMachine, Instruction::{Inc, DecJump, Halt}, step, 
run, │
│  halts                                                                       
│
│ - ceer.rs: CEER, ceer_wf, declared_pair, ceer_equiv                          
│
│ - ceer_two_gen.rs: universal_word(n), lemma_two_gen_forward (backward 
NOT    │
│ proved)                                                                      
│
│ - ceer_benign.rs: the target axiom                                           
│
│                                                                              
│
│ Construction Plan                                                            
│
│                                                                              
│
│ Phase 0: Modular Machine Specs                                               
│
│                                                                              
│
│ New file: verus-computability-theory/src/modular_machine.rs (~500-800 
lines) │
│                                                                              
│
│ Convert Minsky counter machines to modular machines. Register values 
(r0,    │
│ ..., rk) encoded as alpha = p0^r0 * p1^r1 * ... (prime power                 
│
│ representation). Inc(r_i) becomes multiply-by-p_i. DecJump(r_i, target)      
│
│ splits into: residue 0 mod p_i → divide, else → identity + jump.             
│
│                                                                              
│
│ struct ModularMachine { num_states: nat, quadruples: 
Seq<ModularQuadruple> } │
│ struct ModularQuadruple { state: nat, residue: nat, modulus: nat,            
│
│ next_state: nat, alpha_op: ModOp, beta_op: ModOp }                           
│
│ enum ModOp { Mul(nat), Div(nat), Id }                                        
│
│                                                                              
│
│ spec fn modular_step(mm, state, alpha, beta) -> Option<(nat, nat, nat)>      
│
│ spec fn modular_halts(mm, state, alpha, beta) -> bool                        
│
│                                                                              
│
│ Axiom (conversion): axiom_register_to_modular(m: RegisterMachine) —          
│
│ axiomatized initially. Requires number theory (prime factorization, 
CRT) not │
│  yet in codebase. Can be filled in later.                                    
│
│                                                                              
│
│ Phase 1: Machine Group via HNN Tower                                         
│
│                                                                              
│
│ New file: verus-group-theory/src/machine_group.rs (~800-1200 lines)          
│
│                                                                              
│
│ Build f.p. group G_M encoding modular machine M's computations:              
│
│ - Generators: q_0..q_{s-1} (states), a, b (registers), t_0..t_{k-1} 
(stable  │
│ letters)                                                                     
│
│ - Each quadruple becomes an HNN association: t_k conjugates q_i * a^r 
to q_j │
│  * (result)                                                                  
│
│ - Tower of HNN extensions, one per quadruple, using existing                 
│
│ HNNData/hnn_presentation                                                     
│
│                                                                              
│
│ spec fn machine_base_group(mm: ModularMachine) -> Presentation               
│
│ spec fn machine_group(mm: ModularMachine) -> Presentation                    
│
│ spec fn config_word(mm, state, alpha, beta) -> Word                          
│
│                                                                              
│
│ Key lemma: lemma_machine_step_gives_equiv — one machine step → equiv 
in G_M  │
│ (via lemma_hnn_conjugation)                                                  
│
│                                                                              
│
│ Phase 2: Faithfulness via Britton                                            
│
│                                                                              
│
│ New file: verus-group-theory/src/machine_group_faithful.rs (~1500-2500       
│
│ lines)                                                                       
│
│                                                                              
│
│ Forward (~500 lines): M runs C1→C2 implies config_word(C1) ≡ 
config_word(C2) │
│  in G_M. Induction on steps.                                                 
│
│                                                                              
│
│ Backward (~1000-2000 lines): config_word(C1) ≡ config_word(C2) in G_M        
│
│ implies computations connected. Uses axiom_britton_lemma at each HNN 
tower   │
│ level: either the derivation stays in the base (recurse inward) or uses 
a    │
│ stable letter (which corresponds to a machine step).                         
│
│                                                                              
│
│ Must verify hnn_associations_isomorphic(data) at each level — follows 
from   │
│ modular operations being invertible (multiply by c inverted by divide 
by c). │
│                                                                              
│
│ Phase 3: Benign Witness Construction (hardest phase)                         
│
│                                                                              
│
│ New file: verus-computability-theory/src/ceer_benign_construction.rs         
│
│ (~2000-3000 lines)                                                           
│
│                                                                              
│
│ Construct BenignWitness showing CEER relators (as F_2 words via              
│
│ universal_word) form a benign subgroup of F_2.                               
│
│                                                                              
│
│ Overgroup K: G_MM * F_2 (free product) + finitely many identification        
│
│ relators connecting machine outputs to F_2 universal words. Still 
finitely   │
│ presented.                                                                   
│
│                                                                              
│
│ Embedding: F_2 → K via the free product right-embedding.                     
│
│                                                                              
│
│ L-generators: Computation-advancing stable letters + initial config 
template │
│  + output-reading identifiers. Finite because M has finitely many            
│
│ instructions.                                                                
│
│                                                                              
│
│ 10 clauses of benign_witness_valid: The critical ones:                       
│
│ - Injective: Britton's lemma + free product normal forms                     
│
│ - Forward subgroup: CEER relator → halting computation → traceable in 
G_MM   │
│ via stable letters → element of L                                            
│
│ - Backward subgroup: element of L → factors through actual 
computations      │
│ (Britton) → produces CEER pairs → relators                                   
│
│ - Quotient forward/backward: from forward/backward +                         
│
│ injectivity/preservation                                                     
│
│                                                                              
│
│ Phase 4: Assembly                                                            
│
│                                                                              
│
│ Modified file: verus-computability-theory/src/ceer_benign.rs                 
│
│                                                                              
│
│ Replace #[verifier::external_body] with real proof:                          
│
│ 1. Extract machine from CEER, convert to modular machine                     
│
│ 2. Build benign witness (Phase 3)                                            
│
│ 3. Apply lemma_rope_trick → get f.p. presentation H + embedding              
│
│ 4. Compose: emb(n) = apply_embedding(rope_trick_emb, universal_word(n))      
│
│ 5. Prove biconditional via forward/backward chains                           
│
│                                                                              
│
│ Phase 4b: Two-Gen Backward Direction                                         
│
│                                                                              
│
│ Modified file: verus-computability-theory/src/ceer_two_gen.rs (+500-800      
│
│ lines)                                                                       
│
│                                                                              
│
│ Prove: universal_word(n) ≡ universal_word(m) in F_2/<> implies 
ceer_equiv(e, │
│  n, m). Uses word_count technique from ceer_group_backward.rs adapted 
to     │
│ 2-generator setting.                                                         
│
│                                                                              
│
│ Alternative: bypass two-gen entirely by constructing the embedding from 
the  │
│ infinite-generator CEER group directly via homomorphism. This avoids 
the     │
│ backward direction but changes Phase 3's construction.                       
│
│                                                                              
│
│ File Summary                                                                 
│
│                                                                              
│
│ File: modular_machine.rs                                                     
│
│ Crate: verus-computability-theory                                            
│
│ Est. Lines: 500-800                                                          
│
│ Purpose: Modular machine specs + conversion axiom                            
│
│ 
────────────────────────────────────────                                     
│
│ File: machine_group.rs                                                       
│
│ Crate: verus-group-theory                                                    
│
│ Est. Lines: 800-1200                                                         
│
│ Purpose: HNN tower encoding computation                                      
│
│ 
────────────────────────────────────────                                     
│
│ File: machine_group_faithful.rs                                              
│
│ Crate: verus-group-theory                                                    
│
│ Est. Lines: 1500-2500                                                        
│
│ Purpose: Forward + backward faithfulness                                     
│
│ 
────────────────────────────────────────                                     
│
│ File: ceer_benign_construction.rs                                            
│
│ Crate: verus-computability-theory                                            
│
│ Est. Lines: 2000-3000                                                        
│
│ Purpose: Benign witness (the core)                                           
│
│                                                                              
│
│ 
┌───────────────────┬───────────────────────────────────────────────────┐    
│
│ │   Modified File   │                      Change                       
│    │
│ 
├───────────────────┼───────────────────────────────────────────────────┤    
│
│ │ ceer_benign.rs    │ Remove external_body, add real proof (~200 
lines) │    │
│ 
├───────────────────┼───────────────────────────────────────────────────┤    
│
│ │ ceer_two_gen.rs   │ Add backward direction (~500-800 lines)           
│    │
│ 
├───────────────────┼───────────────────────────────────────────────────┤    
│
│ │ Both lib.rs files │ Add new modules                                   
│    │
│ 
└───────────────────┴───────────────────────────────────────────────────┘    
│
│                                                                              
│
│ Total: ~6,300-9,700 new lines                                                
│
│                                                                              
│
│ Implementation Order                                                         
│
│                                                                              
│
│ 1. Phase 0 with axiom (unblocks Phase 1, ~300 lines specs)                   
│
│ 2. Phase 1 — machine group (concrete, well-defined)                          
│
│ 3. Phase 2 forward direction (easier half)                                   
│
│ 4. Two-gen backward direction (ceer_two_gen.rs)                              
│
│ 5. Phase 3 — benign witness (hardest, may need design iteration)             
│
│ 6. Phase 2 backward direction (needs Phase 3 to be stable)                   
│
│ 7. Phase 4 — assembly/wiring                                                 
│
│                                                                              
│
│ Risks & Mitigations                                                          
│
│                                                                              
│
│ Phase 3 uncertainty: The exact benign witness construction details need      
│
│ working out during implementation. Textbook proofs aren't constructive       
│
│ enough. Mitigation: Start with concrete 2-state example; use 
Mikaelian's     │
│ explicit algorithm as guide.                                                 
│
│                                                                              
│
│ Britton gaps: 3 assume(false) in britton_proof.rs. Our HNN towers may 
or may │
│  not trigger the unproved k>=4 case. Mitigation: The 2 boundary cases 
(lines │
│  11018, 11059) are being completed by another session. For k>=4, verify 
our  │
│ constructions produce short derivation segments.                             
│
│                                                                              
│
│ Fallback: If Phase 3 is too complex, replace the axiom with the smaller      
│
│ axiom_ceer_relators_benign(e) ensuring is_benign(free_group(2),              
│
│ ceer_relator_words(e)). This decomposes the original axiom into a 
focused    │
│ "benignness of c.e. subgroups" axiom + the proved Rope Trick.                
│
│                                                                              
│
│ Verification                                                                 
│
│                                                                              
│
│ After each phase: mcp verus check crate_name=verus-group-theory and mcp      
│
│ verus check crate_name=verus-computability-theory                            
│
│                                                                              
│
│ Final state: axiom_ceer_embeds_in_fp_group no longer external_body.          
│
│ Remaining axioms:                                                            
│
│ - axiom_enumerator_machine_exists (Church-Turing thesis — intentionally      
│
│ axiomatic)                                                                   
│
│ - axiom_register_to_modular (new, can be proved later with number 
theory     │
│ infrastructure)                                                              
│
│ - Britton assume(false) gaps (being completed separately)   
