import PureInterp
open PureInterp
#print axioms Machine.run_sim
#print axioms Spec.agrees
#print axioms Top.linked_image
#print axioms Top.runOK_of_runSupported
#print axioms Top.loop_correct
#print axioms Top.loop_correct_machine
#print axioms Top.SpecStart.matches
#print axioms Top.spec_result
#print axioms Top.heapNextCell_initial
#eval ((List.range 256).filter fun n => EvmYul.EVM.parseInstr (UInt8.ofNat n) == some .INVALID).length
#eval PureInterp.Image.invalidOpcodes.length
