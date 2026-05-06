#define PY_SSIZE_T_CLEAN
#include <Python.h>

#define QISKIT_C_PYTHON_INTERFACE
#include <qiskit.h>

static const char* const CF_OP_NAME[] = {"Box", "BreakLoop", "ContinueLoop", "ForLoop", "IfElse", "Switch", "While"};
static const char* const CF_CONDITION_TYPE[] = {"Bit", "Reg", "Expr"};
static const char* const EXPR_TYPE[] = {"Unary", "Binary", "Cast", "Value", "Var", "Stretch", "Index"};

void print_circuit(const QkCircuit *, unsigned indent, const QkControlFlowInstruction*);

void inspect_expr(const QkExprNode *expr_node, unsigned indent) {
    QkExprNodeType type = qk_expr_node_type(expr_node);
    printf("%*sEXPR type: %s\n", indent, "", EXPR_TYPE[type]);

    switch (type) {
        case QkExprNodeType_Binary:
        {
            QkBinaryExpr binary;
            qk_expr_binary(expr_node, &binary);

            printf("%*s BINARY: %d, %d, %d\n", indent, "", binary.op, binary.ty, binary.constant);
            
            inspect_expr(binary.left, indent + 2);
            inspect_expr(binary.right, indent + 2);
        }
        break;
        
        default:
            // TODO:
    }
}

void inspect_condition(const QkControlFlowInstruction *cf_inst, unsigned indent) {
    QkControlFlowType cf_type = qk_control_flow_type(cf_inst);
    printf("%*s CONTROL FLOW: %s\n", indent, ">", CF_OP_NAME[cf_type]);

    switch (cf_type) {
        case QkControlFlowType_IfElse:
        case QkControlFlowType_While:
            QkConditionType condition_type = qk_control_flow_condition_type(cf_inst);
            printf("%*s condition type: %s\n", indent, "", CF_CONDITION_TYPE[condition_type]);
            if (condition_type == QkConditionType_Expr) { 
                // qk_control_flow_condition(cf_inst); // TODO: remove, just for debug print for now
                inspect_expr(qk_control_flow_condition_expr(cf_inst), indent);
            }
            break;
        case QkControlFlowType_Box:
            break;
        }
}

void inspect_control_flow(const QkControlFlowInstruction *cf_inst, unsigned indent) { 
    inspect_condition(cf_inst, indent);

    uint32_t num_blocks = qk_control_flow_num_blocks(cf_inst);

    for (uint32_t block = 0; block < num_blocks; block++) {
        const QkCircuit *block_circuit = qk_control_flow_block_circuit(cf_inst, block);

        size_t num_instructions = qk_circuit_num_instructions(block_circuit);
        printf("%*s%ld instructions in block #%d\n", indent, "", num_instructions, block);
        
        print_circuit(block_circuit, indent + 2, cf_inst);
    }
}

void print_circuit(const QkCircuit *circuit, unsigned indent, const QkControlFlowInstruction* parent_cf) {
    size_t num_instructions = qk_circuit_num_instructions(circuit);

    for (size_t inst_idx = 0; inst_idx < num_instructions; inst_idx++) { 
        QkCircuitInstruction inst;
        qk_circuit_get_instruction(circuit, inst_idx, &inst);

        QkOperationKind kind = qk_circuit_instruction_kind(circuit, inst_idx);

        if (kind == QkOperationKind_ControlFlow) {
            const QkControlFlowInstruction *cf_inst = qk_circuit_get_control_flow_instruction(circuit, inst_idx, parent_cf);
            inspect_control_flow(cf_inst, indent + 2);
        } else {
            printf("%*s%s ", indent, " ", inst.name);

            // Print qubit/clbit indices with mapping to the top-level circuit taken into account
            const uint32_t *qubit_mapping = parent_cf ? qk_control_flow_qubit_map(parent_cf) : NULL;
            for (uint32_t qubit = 0; qubit < inst.num_qubits; qubit++) {
                uint32_t mapped_qubit = qubit_mapping ? qubit_mapping[inst.qubits[qubit]] : inst.qubits[qubit];
                printf("%d%s", mapped_qubit, qubit < inst.num_qubits - 1 ? ", " : "\n");
            }
            
            const uint32_t *clbit_mapping = parent_cf ? qk_control_flow_clbit_map(parent_cf) : NULL;
            for (uint32_t clbit = 0; clbit < inst.num_clbits; clbit++) {
                uint32_t mapped_clbit = clbit_mapping ? clbit_mapping[inst.clbits[clbit]] : inst.clbits[clbit];
                printf("%d%s", mapped_clbit, clbit < inst.num_clbits - 1 ? ", " : "\n");
            }
        }

        qk_circuit_instruction_clear(&inst);
    }
}

static PyObject *traverse_circuit(PyObject *self, PyObject *ob) {

    QkCircuit *circuit = qk_circuit_borrow_from_python(ob);

    print_circuit(circuit, 2, NULL);

    return Py_None;
}

/* Method table */
static PyMethodDef my_python_ext_funcs[] = {
    {"traverse_circuit", (PyCFunction)traverse_circuit, METH_O, ""},
    {NULL, NULL, 0, NULL}
};

/* Module definition (PEP 3121/384 style) */
static struct PyModuleDef my_qiskit_extmodule = {
    PyModuleDef_HEAD_INIT,
    "my_python_ext",
    "A tiny C extension with add and dot",
    -1,                 // per-interpreter state size, -1 for global state
    my_python_ext_funcs
};

/* Module init function */
PyMODINIT_FUNC PyInit_my_python_ext(void) {
    return PyModule_Create(&my_qiskit_extmodule);
}
