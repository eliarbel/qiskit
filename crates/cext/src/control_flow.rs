use std::ptr;

use qiskit_circuit::bit::ClassicalRegister;
use qiskit_circuit::circuit_data::CircuitData;
use qiskit_circuit::operations::{ControlFlow, ControlFlowInstruction, Condition};
use qiskit_circuit::classical::expr::Expr;

use crate::pointers::{const_ptr_as_ref, mut_ptr_as_ref};

pub struct CControlFlowInstruction { 
    /// The circuit this control-flow instruction lives in
    circuit: *const CircuitData, // TODO: safety caveats!!
    /// The index of the control flow instruction in the containing circuit
    inst_idx: usize,
    /// Qubit mapping of this instruction qargs w.r.t the top-level circuit
    pub(crate) qubit_map: Vec<u32>, // TODO: store Qubit? consider using Option (and return NULL in the C API getter)
    /// Clbit mapping of this instruction qargs w.r.t the top-level circuit
    pub(crate) clbit_map: Vec<u32>, // TODO: store Clbit? consider using Option (and return NULL in the C API getter)
}

impl CControlFlowInstruction {
    pub fn new(circuit: &CircuitData, inst_idx: usize, qubit_map: Vec<u32>, clbit_map: Vec<u32>) -> Self { 
        Self {
            circuit: circuit as *const CircuitData,
            inst_idx,
            qubit_map,
            clbit_map,
        }
    }
}

#[repr(u8)]
pub enum CControlFlowKind { 
    Box = 0,
    BreakLoop = 1,
    ContinueLoop = 2,
    ForLoop = 3,
    IfElse = 4,
    Switch = 5,
    While = 6,
}

impl CControlFlowKind { 
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


#[repr(C)]
pub struct CConditionBit {
    creg: *mut ClassicalRegister, 
    /// The clbit within the classical register the condition corresponds to
    pub clbit: u32, 
    pub condition: bool,
}

#[repr(C)]
pub struct CConditionReg { // TODO: add _clear function
    creg: *mut ClassicalRegister, 
    /// The clbit within the classical register the condition corresponds to
    pub condition: u64, // TODO: represent BigUint instead
}


#[unsafe(no_mangle)]
pub unsafe extern "C" fn qk_control_flow_kind(cf_inst: *const CControlFlowInstruction) -> CControlFlowKind {
    let cf_inst = unsafe { const_ptr_as_ref(cf_inst) };
    let circuit = unsafe { const_ptr_as_ref(cf_inst.circuit) };
    let instruction = &circuit.data()[cf_inst.inst_idx];

    let cf_inst = instruction.op.try_control_flow().expect("Invalid control flow instruction in the given circuit context");

    CControlFlowKind::from_control_flow_instruction(cf_inst)
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn qk_control_flow_num_blocks(cf_inst: *const CControlFlowInstruction) -> usize {
    let cf_inst = unsafe { const_ptr_as_ref(cf_inst) };
    let circuit = unsafe { const_ptr_as_ref(cf_inst.circuit) };

    let instruction = &circuit.data()[cf_inst.inst_idx];

    instruction.blocks_view().len()
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn qk_control_flow_block_circuit(cf_inst: *const CControlFlowInstruction, block_idx: usize) -> *const CircuitData {
    let cf_inst = unsafe { const_ptr_as_ref(cf_inst) };
    let circuit = unsafe { const_ptr_as_ref(cf_inst.circuit) };
    
    let instruction = &circuit.data()[cf_inst.inst_idx];

    let block_ids = instruction.blocks_view();
    // TODO: SAFETY ALERT, SAFETY ALERT!! all CircuitData objects should be frozen in memory and not mutated at this stage
    &circuit.blocks()[block_ids[block_idx]] as *const CircuitData 
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
pub unsafe extern "C" fn qk_control_flow_condition_type(cf_inst: *const CControlFlowInstruction) -> CConditionType {
    let cf_inst = unsafe { const_ptr_as_ref(cf_inst) };
    let circuit = unsafe { const_ptr_as_ref(cf_inst.circuit) };

    let inst = &circuit.data()[cf_inst.inst_idx];
    let cf_inst = inst.op.try_control_flow().expect("Invalid control flow instruction in the given circuit context");

    match &cf_inst.control_flow {
        ControlFlow::IfElse { condition } | ControlFlow::While { condition } => CConditionType::from_condition(condition),
        _ => panic!("Control flow instruction without a condition")
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn qk_control_flow_condition(cf_inst: *const CControlFlowInstruction) {
    let cf_inst = unsafe { const_ptr_as_ref(cf_inst) };
    let circuit = unsafe { const_ptr_as_ref(cf_inst.circuit) };

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


#[unsafe(no_mangle)]
pub unsafe extern "C" fn qk_control_flow_condition_bit(cf_inst: *const CControlFlowInstruction, cond_bit: *mut CConditionBit) {
    let cf_inst = unsafe { const_ptr_as_ref(cf_inst) };
    let circuit = unsafe { const_ptr_as_ref(cf_inst.circuit) };

    let inst = &circuit.data()[cf_inst.inst_idx];
    let condition = match &inst.op.control_flow().control_flow {
        ControlFlow::IfElse{ condition } | 
        ControlFlow::While{ condition } => condition,
        _ => panic!("A control flow instruction with a condition is expected")
    };

    let Condition::Bit(clbit, cond) = condition else {
        panic!("A Bit condition is expected")
    };

    let cond_bit = unsafe { mut_ptr_as_ref(cond_bit) };
    cond_bit.creg = clbit.owning_register().map_or(ptr::null_mut(), |creg| Box::into_raw(Box::new(creg)));
    cond_bit.clbit = clbit.owning_register_index().unwrap_or_default(); // TODO: handle the case this is anonymous 
    cond_bit.condition = *cond;
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn qk_control_flow_condition_bit_clear(cond_bit: *mut CConditionBit) { 
    // TODO: implement
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn qk_control_flow_condition_register(cf_inst: *const CControlFlowInstruction, cond_reg: *mut CConditionReg) {
    let cf_inst = unsafe { const_ptr_as_ref(cf_inst) };
    let circuit = unsafe { const_ptr_as_ref(cf_inst.circuit) };

    let inst = &circuit.data()[cf_inst.inst_idx];
    let condition = match &inst.op.control_flow().control_flow {
        ControlFlow::IfElse{ condition } | 
        ControlFlow::While{ condition } => condition,
        _ => panic!("A control flow instruction with a condition is expected")
    };

    let Condition::Register(creg, cond) = condition else {
        panic!("A Register condition is expected")
    };

    let cond_reg = unsafe { mut_ptr_as_ref(cond_reg) };
    cond_reg.creg = Box::into_raw(Box::new(creg.clone())); // TODO: should it just be *const ClassicalRegister?
    cond_reg.condition = cond.try_into().unwrap(); // TODO: temporary, should handle BigUint
}


#[unsafe(no_mangle)]
pub unsafe extern "C" fn qk_control_flow_condition_expr(cf_inst: *const CControlFlowInstruction) -> *const Expr {
    let cf_inst = unsafe { const_ptr_as_ref(cf_inst) };
    let circuit = unsafe { const_ptr_as_ref(cf_inst.circuit) };

    let inst = &circuit.data()[cf_inst.inst_idx];
    let expr = match &inst.op.control_flow().control_flow {
        ControlFlow::IfElse{ condition } | 
        ControlFlow::While{ condition } => {
            if let Condition::Expr(expr) = condition {
                expr
            } else {
                panic!("A classical expression condition is expected")
            }
        }
        _ => panic!("A control flow instruction with a condition is expected")
    };

    expr as *const Expr
}

// TODO: add qk_control_flow_*_free functions