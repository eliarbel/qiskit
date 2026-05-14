use std::ptr;
use std::ffi::{CString, c_char};

use qiskit_circuit::bit::ClassicalRegister;
use qiskit_circuit::circuit_data::CircuitData;
use qiskit_circuit::operations::{BoxDuration, CaseSpecifier, Condition, ControlFlow, ControlFlowInstruction, ForCollection, SwitchTarget};
use qiskit_circuit::classical::expr::Expr;

use crate::classical_expr::CDurationInfo;
use crate::pointers::{const_ptr_as_ref, mut_ptr_as_ref};
use num_traits::ToPrimitive;


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

impl From<&ControlFlowInstruction> for CControlFlowKind { 
    fn from(value: &ControlFlowInstruction) -> Self {
        match value.control_flow {
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

// Used both for Condition and SwitchTarget 
#[repr(u8)]
pub enum CConditionType {
    ClBit = 0,
    ClReg = 1,
    Expr = 2, 
}

impl From<&Condition> for CConditionType {
    fn from(value: &Condition) -> Self {
        match value {
            Condition::Bit(_,_) => Self::ClBit,
            Condition::Register(_,_) => Self::ClReg,
            Condition::Expr(_) => Self::Expr,
        }
    }
}

impl From<&SwitchTarget> for CConditionType {
    fn from(value: &SwitchTarget) -> Self {
        match value {
            SwitchTarget::Bit(_) => Self::ClBit, 
            SwitchTarget::Register(_) => Self::ClReg,
            SwitchTarget::Expr(_) => Self::Expr,
        }
    }
}


#[repr(C)]
pub struct CConditionBitInfo { 
    pub clbit: u32, 
    pub condition: bool,
}

#[repr(C)]
pub struct CConditionRegInfo {
    creg: *const ClassicalRegister, 
    pub condition: u64, // TODO: coming from BigUint
}

#[repr(u8)]
pub enum CBoxDurationType {
    NoDuration = 0, 
    Duration = 1,
    Expr = 2,
}

impl From<Option<&BoxDuration>> for CBoxDurationType {
    fn from(value: Option<&BoxDuration>) -> Self {
        match value {
            None => Self::NoDuration,
            Some(BoxDuration::Duration(_)) => Self::Duration,
            Some(BoxDuration::Expr(_)) => Self::Expr,
        }
    }
}

#[repr(C)] 
pub struct CSwitchCaseLabels{
    labels: *const u64,
    num_labels: usize,
}
// TODO: document safety: immutable-only views valid as long as cf_inst lives
// TODO: add a helper function for extracting CircuitData and PackedInstruction from CControlFlowInstruction

#[unsafe(no_mangle)]
pub unsafe extern "C" fn qk_control_flow_kind(cf_inst: *const CControlFlowInstruction) -> CControlFlowKind {
    let cf_inst = unsafe { const_ptr_as_ref(cf_inst) };
    let circuit = unsafe { const_ptr_as_ref(cf_inst.circuit) };
    let instruction = &circuit.data()[cf_inst.inst_idx]; // TODO: should always be valid, as CControlFlowInstruction invariant

    let cf_inst = instruction.op.try_control_flow()
        .expect("TODO");

    CControlFlowKind::from(cf_inst)
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn qk_control_flow_num_blocks(cf_inst: *const CControlFlowInstruction) -> usize {
    let cf_inst = unsafe { const_ptr_as_ref(cf_inst) };
    let circuit = unsafe { const_ptr_as_ref(cf_inst.circuit) };

    let instruction = &circuit.data()[cf_inst.inst_idx]; // TODO: should always be valid, as CControlFlowInstruction invariant

    instruction.blocks_view().len()
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn qk_control_flow_block_circuit(cf_inst: *const CControlFlowInstruction, block_idx: usize) -> *const CircuitData {
    let cf_inst = unsafe { const_ptr_as_ref(cf_inst) };
    let circuit = unsafe { const_ptr_as_ref(cf_inst.circuit) };
    
    let instruction = &circuit.data()[cf_inst.inst_idx]; // TODO: should always be valid, as CControlFlowInstruction invariant

    let block_ids = instruction.blocks_view();
    let block_circuit = &circuit.blocks()[block_ids[block_idx]]; // TODO: handle edge cases
    ptr::from_ref(block_circuit)
}


#[unsafe(no_mangle)]
pub unsafe extern "C" fn qk_control_flow_qubit_map(cf_inst: *const CControlFlowInstruction) -> *const u32 {
    let cf_inst = unsafe{ const_ptr_as_ref(cf_inst) };

    cf_inst.qubit_map.as_ptr()
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn qk_control_flow_clbit_map(cf_inst: *const CControlFlowInstruction) -> *const u32 {
    let cf_inst = unsafe{ const_ptr_as_ref(cf_inst) };

    cf_inst.clbit_map.as_ptr()
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn qk_control_flow_condition_type(cf_inst: *const CControlFlowInstruction) -> CConditionType {
    let cf_inst = unsafe { const_ptr_as_ref(cf_inst) };
    let circuit = unsafe { const_ptr_as_ref(cf_inst.circuit) };

    let inst = &circuit.data()[cf_inst.inst_idx]; // TODO: should always be valid, as CControlFlowInstruction invariant

    let cf_inst = inst.op.try_control_flow()
        .expect("TODO");

    match &cf_inst.control_flow {
        ControlFlow::IfElse { condition } | ControlFlow::While { condition } => CConditionType::from(condition),
        _ => panic!("TODO")
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn qk_control_flow_condition_bit_info(cf_inst: *const CControlFlowInstruction) -> CConditionBitInfo {
    let cf_inst = unsafe { const_ptr_as_ref(cf_inst) };
    let circuit = unsafe { const_ptr_as_ref(cf_inst.circuit) };

    let inst = &circuit.data()[cf_inst.inst_idx]; // TODO: should always be valid, as CControlFlowInstruction invariant

    let condition = match &inst.op.control_flow().control_flow {
        ControlFlow::IfElse{ condition } | 
        ControlFlow::While{ condition } => condition,
        _ => panic!("TODO")
    };

    let Condition::Bit(clbit, cond) = condition else {
        panic!("TODO")
    };

    CConditionBitInfo {
        clbit: circuit.clbit_index(clbit).expect("TODO"),
        condition: *cond,
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn qk_control_flow_condition_reg_info(cf_inst: *const CControlFlowInstruction) -> CConditionRegInfo {
    let cf_inst = unsafe { const_ptr_as_ref(cf_inst) };
    let circuit = unsafe { const_ptr_as_ref(cf_inst.circuit) };

    let inst = &circuit.data()[cf_inst.inst_idx]; // TODO: should always be valid, as CControlFlowInstruction invariant

    let condition = match &inst.op.control_flow().control_flow {
        ControlFlow::IfElse{ condition } | 
        ControlFlow::While{ condition } => condition,
        _ => panic!("TODO")
    };

    let Condition::Register(creg, cond) = condition else {
        panic!("TODO")
    };

    CConditionRegInfo {
        creg: creg as *const ClassicalRegister,
        condition: cond.try_into().expect("TODO"), // TODO: handle BigUint
    }
}


#[unsafe(no_mangle)]
pub unsafe extern "C" fn qk_control_flow_condition_expr(cf_inst: *const CControlFlowInstruction) -> *const Expr {
    let cf_inst = unsafe { const_ptr_as_ref(cf_inst) };
    let circuit = unsafe { const_ptr_as_ref(cf_inst.circuit) };

    let inst = &circuit.data()[cf_inst.inst_idx]; // TODO: should always be valid, as CControlFlowInstruction invariant

    let expr = match &inst.op.control_flow().control_flow {
        ControlFlow::IfElse{ condition } | 
        ControlFlow::While{ condition } => {
            if let Condition::Expr(expr) = condition {
                expr
            } else {
                panic!("TODO")
            }
        }
        _ => panic!("TODO")
    };

    ptr::from_ref(expr)
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn qk_control_flow_box_duration_type(cf_inst: *const CControlFlowInstruction) -> CBoxDurationType {
    let cf_inst = unsafe { const_ptr_as_ref(cf_inst) };
    let circuit = unsafe { const_ptr_as_ref(cf_inst.circuit) };

    let inst = &circuit.data()[cf_inst.inst_idx]; // TODO: should always be valid, as CControlFlowInstruction invariant

    let cf_inst = inst.op.try_control_flow()
        .expect("TODO");

    let ControlFlow::Box { duration, .. } = &cf_inst.control_flow else {panic!("TODO")};

    CBoxDurationType::from(duration.as_ref())
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn qk_control_flow_box_duration_info(
    cf_inst: *const CControlFlowInstruction) -> CDurationInfo {
    let cf_inst = unsafe { const_ptr_as_ref(cf_inst) };
    let circuit = unsafe { const_ptr_as_ref(cf_inst.circuit) };

    let inst = &circuit.data()[cf_inst.inst_idx]; // TODO: should always be valid, as CControlFlowInstruction invariant

    let cf_inst = inst.op.try_control_flow()
        .expect("TODO");

    let ControlFlow::Box {duration: Some(qiskit_circuit::operations::BoxDuration::Duration(duration)), ..} = 
        &cf_inst.control_flow else {panic!("TODO")};
    
    CDurationInfo::from(duration)
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn qk_control_flow_box_duration_expr(
    cf_inst: *const CControlFlowInstruction
) -> *const Expr {
    let cf_inst = unsafe { const_ptr_as_ref(cf_inst) };
    let circuit = unsafe { const_ptr_as_ref(cf_inst.circuit) };

    let inst = &circuit.data()[cf_inst.inst_idx]; // TODO: should always be valid, as CControlFlowInstruction invariant

    let cf_inst = inst.op.try_control_flow()
        .expect("TODO");

    
    let ControlFlow::Box { duration: Some(qiskit_circuit::operations::BoxDuration::Expr(expr)), .. } = 
        &cf_inst.control_flow else {panic!("TODO")};

    ptr::from_ref(expr)
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn qk_control_flow_loop_collection(cf_inst: *const CControlFlowInstruction, 
    out_collection: *mut *const usize) -> usize {
    let cf_inst = unsafe { const_ptr_as_ref(cf_inst) };
    let circuit = unsafe { const_ptr_as_ref(cf_inst.circuit) };

    let inst = &circuit.data()[cf_inst.inst_idx]; // TODO: should always be valid, as CControlFlowInstruction invariant

    let cf_inst = inst.op.try_control_flow()
        .expect("TODO");
    
    let ControlFlow::ForLoop { collection: ForCollection::List(elements), .. } = &cf_inst.control_flow 
        else {panic!("TODO")};

    unsafe{ *out_collection = elements.as_ptr() };
    elements.len()
}

// TODO: This function is used both for querying and retrieving the existence of a symbol 
// (and possibly and index) thus, returning NULL for the name or -1 for index is not an error
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qk_control_flow_loop_symbol(cf_inst: *const CControlFlowInstruction, 
    out_name: *mut *mut c_char) -> i64 {
    let cf_inst = unsafe { const_ptr_as_ref(cf_inst) };
    let circuit = unsafe { const_ptr_as_ref(cf_inst.circuit) };

    let inst = &circuit.data()[cf_inst.inst_idx]; // TODO: should always be valid, as CControlFlowInstruction invariant

    let cf_inst = inst.op.try_control_flow()
        .expect("TODO");
    
    let (name, index) = if let ControlFlow::ForLoop {loop_param: Some(symbol), .. } = &cf_inst.control_flow {
        (
            CString::new(symbol.name())
                .map_or(std::ptr::null_mut(), |name| name.into_raw()),
            symbol.index.map_or(-1, |i| i as i64)
        )
    } else {
        (ptr::null_mut(), -1)            
    };

    unsafe{ *out_name = name };
    index
}


#[unsafe(no_mangle)]
pub unsafe extern "C" fn qk_control_flow_switch_target_type(cf_inst: *const CControlFlowInstruction) -> CConditionType {
    let cf_inst = unsafe { const_ptr_as_ref(cf_inst) };
    let circuit = unsafe { const_ptr_as_ref(cf_inst.circuit) };

    let inst = &circuit.data()[cf_inst.inst_idx]; // TODO: should always be valid, as CControlFlowInstruction invariant
    
    let Some(ControlFlowInstruction{control_flow: ControlFlow::Switch { target, ..}, ..})
         = inst.op.try_control_flow() else { panic!("TODO") };

    CConditionType::from(target)
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn qk_control_flow_switch_target_bit(cf_inst: *const CControlFlowInstruction) -> u32 {
    let cf_inst = unsafe { const_ptr_as_ref(cf_inst) };
    let circuit = unsafe { const_ptr_as_ref(cf_inst.circuit) };

    let inst = &circuit.data()[cf_inst.inst_idx]; // TODO: should always be valid, as CControlFlowInstruction invariant
    
    let Some(ControlFlowInstruction{control_flow: ControlFlow::Switch { target: SwitchTarget::Bit(clbit), .. }, ..})
         = inst.op.try_control_flow() else { panic!("TODO") };

    let Some(clbit) = circuit.clbit_index(clbit) else { panic!("TODO") };

    clbit
}

// TODO: assumes SwitchTarget::Register
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qk_control_flow_switch_target_register(cf_inst: *const CControlFlowInstruction) -> *const ClassicalRegister {
    let cf_inst = unsafe { const_ptr_as_ref(cf_inst) };
    let circuit = unsafe { const_ptr_as_ref(cf_inst.circuit) };

    let inst = &circuit.data()[cf_inst.inst_idx]; // TODO: should always be valid, as CControlFlowInstruction invariant
    
    let Some(ControlFlowInstruction{control_flow: ControlFlow::Switch { target: SwitchTarget::Register(reg), .. }, ..})
         = inst.op.try_control_flow() else { panic!("TODO") };

    ptr::from_ref(reg)
}

// TODO: assumes target is SwitchTarget::Expr
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qk_control_flow_switch_target_expr(cf_inst: *const CControlFlowInstruction) -> *const Expr {
    let cf_inst = unsafe { const_ptr_as_ref(cf_inst) };
    let circuit = unsafe { const_ptr_as_ref(cf_inst.circuit) };

    let inst = &circuit.data()[cf_inst.inst_idx]; // TODO: should always be valid, as CControlFlowInstruction invariant
    
    let Some(ControlFlowInstruction{control_flow: ControlFlow::Switch { target: SwitchTarget::Expr(expr), .. }, ..})
         = inst.op.try_control_flow() else { panic!("TODO") };

    ptr::from_ref(expr)
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn qk_control_flow_switch_num_cases(cf_inst: *const CControlFlowInstruction) -> u32 {
    let cf_inst = unsafe { const_ptr_as_ref(cf_inst) };
    let circuit = unsafe { const_ptr_as_ref(cf_inst.circuit) };

    let inst = &circuit.data()[cf_inst.inst_idx]; // TODO: should always be valid, as CControlFlowInstruction invariant
    
    let Some(ControlFlowInstruction{control_flow: ControlFlow::Switch { cases, .. }, ..})
         = inst.op.try_control_flow() else { panic!("TODO") };

    *cases
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn qk_control_flow_switch_is_case_default(cf_inst: *const CControlFlowInstruction, case_idx: usize) -> bool {
    let cf_inst = unsafe { const_ptr_as_ref(cf_inst) };
    let circuit = unsafe { const_ptr_as_ref(cf_inst.circuit) };

    let inst = &circuit.data()[cf_inst.inst_idx]; // TODO: should always be valid, as CControlFlowInstruction invariant
    
    let Some(ControlFlowInstruction{control_flow: ControlFlow::Switch { label_spec, .. }, ..})
         = inst.op.try_control_flow() else { panic!("TODO") };
        
    matches!(label_spec[case_idx].first(), Some(CaseSpecifier::Default))
}

// TODO: assumes: ControlFlow::Switch and non-default case
#[unsafe(no_mangle)]
pub unsafe extern "C" fn qk_control_flow_switch_case_labels(cf_inst: *const CControlFlowInstruction, 
    case_idx: usize, out_labels: *mut CSwitchCaseLabels ) {
    let cf_inst = unsafe { const_ptr_as_ref(cf_inst) };
    let circuit = unsafe { const_ptr_as_ref(cf_inst.circuit) };

    let inst = &circuit.data()[cf_inst.inst_idx]; // TODO: should always be valid, as CControlFlowInstruction invariant
    
    let Some(ControlFlowInstruction{control_flow: ControlFlow::Switch { label_spec, .. }, ..})
         = inst.op.try_control_flow() else { panic!("TODO") };

    let labels = label_spec[case_idx]
                .iter()
                .filter_map(|l| {
                    if let CaseSpecifier::Uint(label) = l {
                        label.to_u64()
                    } else {panic!("TODO")} // TODO: Default should not be present in the label_spec of a non-default case
                })
                .collect::<Vec<u64>>()
                .into_boxed_slice();

    let out_case_labels = unsafe{ mut_ptr_as_ref(out_labels) };
    out_case_labels.num_labels = labels.len();
    out_case_labels.labels = Box::into_raw(labels) as *const u64;
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn qk_control_flow_switch_case_labels_clear(labels: *mut CSwitchCaseLabels) {
    let labels = unsafe { mut_ptr_as_ref(labels) };
    
    if !labels.labels.is_null() && labels.num_labels > 0 {
        drop(unsafe {
            Box::from_raw(std::slice::from_raw_parts_mut(
                labels.labels as *mut u64,
                labels.num_labels,
            ))
        });
        
        labels.labels = std::ptr::null();
        labels.num_labels = 0;
    }
}
