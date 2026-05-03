use qiskit_circuit::circuit_data::CircuitData;
use qiskit_circuit::operations::{ControlFlow, ControlFlowInstruction, Condition};

use crate::pointers::const_ptr_as_ref;

pub struct CControlFlowInstruction { 
    /// The index of the control flow instruction in its containing circuit
    inst_idx: usize,
    /// Qubit mapping of this instruction qargs w.r.t the top-level circuit
    pub(crate) qubit_map: Vec<u32>, // TODO: use Qubit? consider using Option (and return NULL in the C API getter)
    /// Clbit mapping of this instruction qargs w.r.t the top-level circuit
    pub(crate) clbit_map: Vec<u32>, // TODO: Use Clbit? consider using Option (and return NULL in the C API getter)
}

impl CControlFlowInstruction {
    pub fn new(inst_idx: usize, qubit_map: Vec<u32>, clbit_map: Vec<u32>) -> Self { 
        Self {
            inst_idx,
            qubit_map,
            clbit_map,
        }
    }
}

#[repr(u8)]
pub enum CControlFlowType { 
    Box = 0,
    BreakLoop = 1,
    ContinueLoop = 2,
    ForLoop = 3,
    IfElse = 4,
    Switch = 5,
    While = 6,
}

impl CControlFlowType { 
    fn from_control_flow_instruction(cf_inst: &ControlFlowInstruction) -> Self {
        match cf_inst.control_flow {
            ControlFlow::Box {..} => Self::Box,
            ControlFlow::BreakLoop => Self::BreakLoop,
            ControlFlow::ContinueLoop => Self::ContinueLoop,
            ControlFlow::ForLoop {..} => Self::ForLoop,
            ControlFlow::IfElse {..} => Self::IfElse,
            ControlFlow::Switch {..} => Self::Switch,
            ControlFlow::While {..} => Self::While,
        }
    }
}

#[repr(u8)]
pub enum CConditionType {
    ClBit = 0,
    ClReg = 1,
    Expr = 2, 
}

impl CConditionType {
    pub fn from_condition(condition: &Condition) -> Self {
        match condition {
            Condition::Bit(_,_) => Self::ClBit,
            Condition::Register(_,_) => Self::ClReg,
            Condition::Expr(_) => Self::Expr,
        }
    }
}


#[unsafe(no_mangle)]
pub unsafe extern "C" fn qk_control_flow_type(cf_inst: *const CControlFlowInstruction, circuit: *const CircuitData) -> CControlFlowType {
    let cf_inst = unsafe { const_ptr_as_ref(cf_inst) };
    let circuit = unsafe { const_ptr_as_ref(circuit) };
    let instruction = &circuit.data()[cf_inst.inst_idx];

    let cf_inst = instruction.op.try_control_flow().expect("Invalid control flow instruction in the given circuit context");

    CControlFlowType::from_control_flow_instruction(cf_inst)
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn qk_control_flow_num_blocks(cf_inst: *const CControlFlowInstruction, circuit: *const CircuitData) -> usize {
    let cf_inst = unsafe { const_ptr_as_ref(cf_inst) };
    let circuit = unsafe { const_ptr_as_ref(circuit) };
    let instruction = &circuit.data()[cf_inst.inst_idx];

    instruction.blocks_view().len()
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn qk_control_flow_block_circuit(cf_inst: *const CControlFlowInstruction, circuit: *const CircuitData, block_idx: usize) -> *mut CircuitData {
    let cf_inst = unsafe { const_ptr_as_ref(cf_inst) };
    let circuit = unsafe { const_ptr_as_ref(circuit) };
    let instruction = &circuit.data()[cf_inst.inst_idx];

    let blocks = instruction.blocks_view();
    let block_circuit = &circuit.blocks()[blocks[block_idx]];
    
    Box::into_raw(Box::new(block_circuit.clone())) // TODO: use a cheaper clone
}

// TODO: document safety": immutable-only view valid as long as cf_inst lives
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qk_control_flow_qubit_map(cf_inst: *const CControlFlowInstruction) -> *const u32 {
    let cf_inst = unsafe{ const_ptr_as_ref(cf_inst) };

    cf_inst.qubit_map.as_ptr()
}

// TODO: document safety: immutable-only view valid as long as cf_inst lives
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qk_control_flow_clbit_map(cf_inst: *const CControlFlowInstruction) -> *const u32 {
    let cf_inst = unsafe{ const_ptr_as_ref(cf_inst) };

    cf_inst.clbit_map.as_ptr()
}


#[unsafe(no_mangle)]
pub unsafe extern "C" fn qk_control_flow_condition_type(cf_inst: *const CControlFlowInstruction, circuit: *const CircuitData) -> CConditionType {
    let cf_inst = unsafe { const_ptr_as_ref(cf_inst) };
    let circuit = unsafe { const_ptr_as_ref(circuit) };

    let inst = &circuit.data()[cf_inst.inst_idx];
    let cf_inst = inst.op.try_control_flow().expect("Invalid control flow instruction in the given circuit context");

    match &cf_inst.control_flow {
        ControlFlow::IfElse { condition } | ControlFlow::While { condition } => CConditionType::from_condition(condition),
        _ => panic!("Control flow instruction without a condition")
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn qk_control_flow_condition(cf_inst: *const CControlFlowInstruction, circuit: *const CircuitData) {
    let cf_inst = unsafe { const_ptr_as_ref(cf_inst) };
    let circuit = unsafe { const_ptr_as_ref(circuit) };
    
    let inst = &circuit.data()[cf_inst.inst_idx];

    match inst.op.view() { 
        qiskit_circuit::operations::OperationRef::ControlFlow(cf_op) => {
            match &cf_op.control_flow { 
                ControlFlow::IfElse { condition } | 
                ControlFlow::While { condition } => {
                    match condition {
                        Condition::Register(r,i) =>  {
                            println!("# {:?} {:?}", r, i);
                        }
                        Condition::Bit(b, i) => {
                            println!("# {:?} {:?}", b, i);

                        }
                        Condition::Expr(expr) => {
                            println!("EXPR {:?}", expr);
                        }
                    }
                },
                _ => unimplemented!()
            }
        },
        _ => unimplemented!()
    }
}

// TODO: add qk_control_flow_*_free functions