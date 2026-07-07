◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻  
*reference: copy pasted and edited from collaboration with computer agents   
not verified, non-machine checked, and maybe depends on basic axioms  
◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻  
>


			In Dobbertin's paper, 
			
				"L" is fixed once at the start of §3:
				
				 "let L = F₂ⁿ" 
					 (the field GF(2ⁿ)).
					 
				Theorem 5 then reads 
					
						"q^(ε) is a permutation polynomial on L", 
						
					so its domain L is that GF(2ⁿ).
					
				"F" appears as F₂
					 (the prime field)
					 
					and in "F₂ⁿ" itself 
					— the notation Fq for finite fields.
					
				So Theorem 5 concerns the polynomial 
					
						q^(ε) acting on L = F₂ⁿ,
						
							 an extension of F = F₂.





.  
.  
.  
.  
.  



				"gadget" is an informal term for a small, 
				self-contained construction
					 (often a reusable auxiliary object,
					  structure, 
					  or encoding) 
				  
				  built to bridge a gap 
				  or make a proof/reduction work. 
				  
				  In combinatorics and complexity 
				  it's a local widget wired into a bigger argument;
				  
				   in Lean formalization it loosely means 
				   
					   a helper definition or lemma packaged 
					   to plug into a larger proof.



.  
.  
.  
.  
.  





					In the PDF 
						"Dobbertin — Kasami Power Functions...", 
						
		look at Section 3
			 ("Inverse Kasami Permutation Polynomials and Applications"). 
			 
			 The 
				 recursive gadget A_i, B_i 
					 is defined just before Theorem 6, 
						 and 
							 R(z) = ∑{i=1}^{k'} A_i(z) + B{k'}(z)
								 appears right there. 
							
				Theorem 6 states 
					q⁻¹(1/y)=R(y); 
					
				Theorem 8 gives 
					the trace description B={Tr R=0}.
				
.  
.  
.  
.  
.  
