use crate::classical::expr;
use crate::object_registry::ObjectRegistry;
use crate::{Stretch, Var};
use indexmap::IndexMap;

use pyo3::exceptions::PyValueError;
use pyo3::prelude::*;
use pyo3::types::PyTuple;
use pyo3::IntoPyObjectExt;

#[derive(Copy, Clone, Debug, PartialEq)]
pub enum VarType {
    Input = 0,
    Capture = 1,
    Declare = 2,
}

#[derive(Copy, Clone, Debug, PartialEq)]
pub enum StretchType {
    Capture = 0,
    Declare = 1,
}
#[derive(Clone, Debug)]
pub struct VarStretchContainer {
    // Variables registered in the container
    vars: ObjectRegistry<Var, expr::Var>,
    // Stretches registered in the container
    stretches: ObjectRegistry<Stretch, expr::Stretch>,
    // Variable identifiers, in order of their addition to the container
    identifier_info: IndexMap<String, IdentifierInfo>,

    // Var indices stored in the container, in order of insertion for each type
    var_indices: [Vec<Var>; 3],

    // Stretch indices stored in the container, in order of insertion for each type
    stretch_indices: [Vec<Stretch>; 2],
}

impl VarStretchContainer {
    pub fn new() -> Self {
        VarStretchContainer {
            vars: ObjectRegistry::new(),
            stretches: ObjectRegistry::new(),
            identifier_info: IndexMap::default(),
            var_indices: [Vec::new(), Vec::new(), Vec::new()],
            stretch_indices: [Vec::new(), Vec::new()],
        }
    }

    pub fn with_capacity(num_vars: Option<usize>, num_stretches: Option<usize>) -> Self {
        let num_vars = num_vars.unwrap_or_default();
        let num_stretches = num_stretches.unwrap_or_default();
        VarStretchContainer {
            vars: ObjectRegistry::with_capacity(num_vars),
            stretches: ObjectRegistry::with_capacity(num_stretches),
            identifier_info: IndexMap::with_capacity(num_vars + num_stretches),
            var_indices: [Vec::new(), Vec::new(), Vec::new()],
            stretch_indices: [Vec::new(), Vec::new()],
        }
    }

    pub fn to_pickle(
        &self,
        py: Python,
    ) -> (Vec<(String, PyObject)>, Vec<expr::Var>, Vec<expr::Stretch>) {
        (
            self.identifier_info
                .iter()
                .map(|(k, v)| (k.clone(), v.clone().to_pickle(py).unwrap()))
                .collect::<Vec<(String, PyObject)>>(),
            self.vars.objects().clone(),
            self.stretches.objects().clone(),
        )
    }

    pub fn from_pickle(
        py: Python,
        identifiers: Vec<(String, PyObject)>, // TODO: maybe jest accept iterators?
        vars: Vec<expr::Var>,
        stretches: Vec<expr::Stretch>,
    ) -> PyResult<Self> {
        let mut res = VarStretchContainer::with_capacity(Some(vars.len()), Some(stretches.len()));

        for identifier_info in identifiers {
            let id_info = IdentifierInfo::from_pickle(identifier_info.1.bind(py))?;
            match &id_info {
                IdentifierInfo::Stretch(stretch_info) => {
                    res.stretch_indices[stretch_info.type_ as usize].push(stretch_info.stretch);
                }
                IdentifierInfo::Var(var_info) => {
                    res.var_indices[var_info.type_ as usize].push(var_info.var);
                }
            }

            res.identifier_info.insert(identifier_info.0, id_info);
        }

        for var in vars {
            res.vars.add(var, false)?;
        }

        for stretch in stretches {
            res.stretches.add(stretch, false)?;
        }

        Ok(res)
    }

    /// Clones this container and converts all variables and stretches to captures.
    pub fn clone_as_captures(&self) -> Result<Self, String> {
        let mut res = VarStretchContainer {
            vars: ObjectRegistry::with_capacity(self.vars.len()),
            stretches: ObjectRegistry::with_capacity(self.stretches.len()),
            identifier_info: IndexMap::with_capacity(self.identifier_info.len()),
            var_indices: [Vec::new(), Vec::with_capacity(self.vars.len()), Vec::new()],
            stretch_indices: [Vec::with_capacity(self.stretches.len()), Vec::new()],
        };

        for info in self.identifier_info.values() {
            match info {
                IdentifierInfo::Stretch(StretchInfo { stretch, .. }) => {
                    let stretch = self
                        .stretches
                        .get(*stretch)
                        .expect("Stretch not found for the specified index")
                        .clone();
                    res.add_stretch(stretch, StretchType::Capture)?;
                }
                IdentifierInfo::Var(VarInfo { var, .. }) => {
                    let var = self
                        .vars
                        .get(*var)
                        .expect("Var not found for the specified index")
                        .clone();
                    res.add_var(var, VarType::Capture)?;
                }
            }
        }

        Ok(res)
    }

    /// Return an immutable view of the variables stored in the container
    pub fn vars(&self) -> &ObjectRegistry<Var, expr::Var> {
        &self.vars
    }

    /// Return an immutable view of the stretches stored in the container
    pub fn stretches(&self) -> &ObjectRegistry<Stretch, expr::Stretch> {
        &self.stretches
    }

    /// TODO: document & test
    pub fn add_var(&mut self, var: expr::Var, var_type: VarType) -> Result<Var, String> {
        let name = {
            let expr::Var::Standalone { name, .. } = &var else {
                return Err(
                    "cannot add variables that wrap `Clbit` or `ClassicalRegister` instances"
                        .to_string(),
                );
            };
            name.clone()
        };

        match self.identifier_info.get(&name) {
            Some(IdentifierInfo::Var(info)) if Some(&var) == self.vars.get(info.var) => {
                return Err("already present in the circuit".to_string());
            }
            Some(_) => {
                return Err("cannot add var as its name shadows an existing identifier".to_string());
            }
            _ => {}
        }

        match var_type {
            VarType::Input
                if self.num_vars(VarType::Capture) > 0
                    || self.num_stretches(StretchType::Capture) > 0 =>
            {
                return Err(
                    "circuits to be enclosed with captures cannot have input variables".to_string(),
                );
            }
            VarType::Capture if !self.var_indices[VarType::Input as usize].is_empty() => {
                // TODO: change to num inputs (also for)
                return Err(
                    "circuits with input variables cannot be enclosed, so they cannot be closures"
                        .to_string(),
                );
            }
            _ => {}
        }

        let idx = self.vars.add(var, true).map_err(|e| e.to_string())?;
        self.var_indices[var_type as usize].push(idx);

        self.identifier_info.insert(
            name,
            IdentifierInfo::Var(VarInfo {
                var: idx,
                type_: var_type,
            }),
        );

        Ok(idx)
    }

    /// TODO: document & test
    pub fn add_stretch(
        &mut self,
        stretch: expr::Stretch,
        stretch_type: StretchType,
    ) -> Result<Stretch, String> {
        // TODO: should we return the Stretch?
        let name = stretch.name.clone();

        match self.identifier_info.get(&name) {
            Some(IdentifierInfo::Stretch(info))
                if Some(&stretch) == self.stretches.get(info.stretch) =>
            {
                return Err("already present in the circuit".to_string());
            }
            Some(_) => {
                return Err(
                    "cannot add stretch as its name shadows an existing identifier".to_string(),
                );
            }
            _ => {}
        }

        if let StretchType::Capture = stretch_type {
            if !self.var_indices[VarType::Input as usize].is_empty() {
                return Err(
                    "circuits with input variables cannot be enclosed, so they cannot be closures"
                        .to_string(),
                );
            }
        }

        let idx = self
            .stretches
            .add(stretch, true)
            .map_err(|e| e.to_string())?;
        self.stretch_indices[stretch_type as usize].push(idx);

        self.identifier_info.insert(
            name,
            IdentifierInfo::Stretch(StretchInfo {
                stretch: idx,
                type_: stretch_type,
            }),
        );

        Ok(idx)
    }

    /// TODO: document & test
    // TODO: make this inline
    pub fn get_var(&self, name: &str) -> Option<&expr::Var> {
        if let Some(IdentifierInfo::Var(var)) = self.identifier_info.get(name) {
            self.vars.get(var.var)
        } else {
            None
        }
    }

    /// TODO: document & test
    // TODO: make this inline
    pub fn get_stretch(&self, name: &str) -> Option<&expr::Stretch> {
        if let Some(IdentifierInfo::Stretch(stretch)) = self.identifier_info.get(name) {
            self.stretches.get(stretch.stretch)
        } else {
            None
        }
    }

    // TODO: make this inline
    pub fn iter_vars(&self, var_type: VarType) -> impl ExactSizeIterator<Item = &expr::Var> {
        self.var_indices[var_type as usize].iter().map(|idx| {
            self.vars
                .get(*idx)
                .expect("Variable with this index should be registered")
        })
    }

    // TODO: make this inline
    pub fn iter_stretches(
        &self,
        stretch_type: StretchType,
    ) -> impl ExactSizeIterator<Item = &expr::Stretch> {
        self.stretch_indices[stretch_type as usize]
            .iter()
            .map(|idx| {
                self.stretches
                    .get(*idx)
                    .expect("Stretch with this index should be registered")
            })
    }

    // TODO: organize the order of the functions here
    // TODO: make this inline
    pub fn num_vars(&self, var_type: VarType) -> usize {
        self.var_indices[var_type as usize].len()
    }

    // TODO: make this inline
    pub fn num_stretches(&self, stretch_type: StretchType) -> usize {
        self.stretch_indices[stretch_type as usize].len()
    }

    // TODO: inline & document
    pub fn has_identifier(&self, name: &str) -> bool {
        self.identifier_info.contains_key(name)
    }

    // TODO: make this inline & document
    pub fn has_var(&self, name: &str) -> bool {
        matches!(self.identifier_info.get(name), Some(IdentifierInfo::Var(_)))
    }

    // TODO: make this inline & document
    pub fn has_var_by_type(&self, name: &str, var_type: VarType) -> bool {
        if let Some(IdentifierInfo::Var(info)) = self.identifier_info.get(name) {
            info.type_ == var_type
        } else {
            false
        }
    }

    // TODO: make this inline & document
    pub fn has_stretch(&self, name: &str) -> bool {
        matches!(
            self.identifier_info.get(name),
            Some(IdentifierInfo::Stretch(_))
        )
    }

    // TODO: make this inline & document
    pub fn has_stretch_by_type(&self, name: &str, stretch_type: StretchType) -> bool {
        if let Some(IdentifierInfo::Stretch(info)) = self.identifier_info.get(name) {
            info.type_ == stretch_type
        } else {
            false
        }
    }
}

impl PartialEq for VarStretchContainer {
    fn eq(&self, other: &Self) -> bool {
        if self.num_vars(VarType::Input) != other.num_vars(VarType::Input)
            || self.num_vars(VarType::Capture) != other.num_vars(VarType::Capture)
            || self.num_vars(VarType::Declare) != other.num_vars(VarType::Declare)
            || self.num_stretches(StretchType::Capture) != other.num_stretches(StretchType::Capture)
            || self.num_stretches(StretchType::Declare) != other.num_stretches(StretchType::Declare)
        {
            return false;
        }

        let mut prev_rhs_stretch_idx = 0usize;
        for (id_name, lhs_id_info) in &self.identifier_info {
            let Some(rhs_id_info) = other.identifier_info.get(id_name) else {
                return false; // Identifier does not exist in other
            };

            match (lhs_id_info, rhs_id_info) {
                (IdentifierInfo::Var(lhs_var_info), IdentifierInfo::Var(rhs_var_info)) => {
                    if lhs_var_info.type_ != rhs_var_info.type_
                        || !other
                            .vars
                            .contains(self.vars.get(lhs_var_info.var).unwrap())
                    {
                        return false; // Not the same var type or UUID
                    }
                }
                (
                    IdentifierInfo::Stretch(lhs_stretch_info),
                    IdentifierInfo::Stretch(rhs_stretch_info),
                ) => {
                    if lhs_stretch_info.type_ != rhs_stretch_info.type_
                        || !other
                            .stretches
                            .contains(self.stretches.get(lhs_stretch_info.stretch).unwrap())
                    {
                        return false; // Not the same stretch type or UUID
                    };

                    // Check whether the declared stretches in the other CircuitData follow the same order of
                    // declaration as in self. This is done by verifying that the indices of the declared stretches
                    // in `identifier_info` of the other CircuitData - which match the stretches encountered during the
                    // iteration here - are monotonically increasing.
                    if let StretchType::Declare = rhs_stretch_info.type_ {
                        let rhs_stretch_idx = other.identifier_info.get_index_of(id_name).unwrap();
                        if rhs_stretch_idx < prev_rhs_stretch_idx {
                            return false;
                        }
                        prev_rhs_stretch_idx = rhs_stretch_idx;
                    }
                }
                _ => {
                    return false;
                }
            }
        }
        true
    }
}

impl Default for VarStretchContainer {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Clone, Debug, PartialEq)]
struct VarInfo {
    pub var: Var,       // TODO: remove pub
    pub type_: VarType, // TODO: remove pub
}

impl VarInfo {
    fn to_pickle(&self, py: Python) -> PyResult<PyObject> {
        (self.var.0, self.type_ as u8).into_py_any(py)
    }

    fn from_pickle(ob: &Bound<PyAny>) -> PyResult<Self> {
        let val_tuple = ob.downcast::<PyTuple>()?;
        Ok(VarInfo {
            var: Var(val_tuple.get_item(0)?.extract()?),
            type_: match val_tuple.get_item(1)?.extract::<u8>()? {
                0 => VarType::Input,
                1 => VarType::Capture,
                2 => VarType::Declare,
                _ => return Err(PyValueError::new_err("Invalid var type")),
            },
        })
    }
}

#[derive(Clone, Debug, PartialEq)]
struct StretchInfo {
    // TODO: remove pub
    pub stretch: Stretch,   // TODO: remove pub
    pub type_: StretchType, // TODO: remove pub
}

impl StretchInfo {
    fn to_pickle(&self, py: Python) -> PyResult<PyObject> {
        (self.stretch.0, self.type_ as u8).into_py_any(py)
    }

    fn from_pickle(ob: &Bound<PyAny>) -> PyResult<Self> {
        let val_tuple = ob.downcast::<PyTuple>()?;
        Ok(StretchInfo {
            stretch: Stretch(val_tuple.get_item(0)?.extract()?),
            type_: match val_tuple.get_item(1)?.extract::<u8>()? {
                0 => StretchType::Capture,
                1 => StretchType::Declare,
                _ => return Err(PyValueError::new_err("Invalid stretch type")),
            },
        })
    }
}

#[derive(Clone, Debug, PartialEq)]
enum IdentifierInfo {
    Stretch(StretchInfo),
    Var(VarInfo),
}

impl IdentifierInfo {
    pub fn to_pickle(&self, py: Python) -> PyResult<PyObject> {
        // TODO: remove pub
        match self {
            IdentifierInfo::Stretch(info) => (0, info.to_pickle(py)?).into_py_any(py),
            IdentifierInfo::Var(info) => (1, info.to_pickle(py)?).into_py_any(py),
        }
    }

    pub fn from_pickle(ob: &Bound<PyAny>) -> PyResult<Self> {
        // TODO: remove pub
        let val_tuple = ob.downcast::<PyTuple>()?;
        match val_tuple.get_item(0)?.extract::<u8>()? {
            0 => Ok(IdentifierInfo::Stretch(StretchInfo::from_pickle(
                &val_tuple.get_item(1)?,
            )?)),
            1 => Ok(IdentifierInfo::Var(VarInfo::from_pickle(
                &val_tuple.get_item(1)?,
            )?)),
            _ => Err(PyValueError::new_err("Invalid identifier info type")),
        }
    }
}
