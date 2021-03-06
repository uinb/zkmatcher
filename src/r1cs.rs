#![allow(unused_variables, dead_code)]
use crate::circuit::Constraint;
use bellman_ce::pairing::{
    bn256::Bn256,
    ff::{Field, PrimeField, PrimeFieldRepr},
    Engine,
};
use byteorder::{LittleEndian, ReadBytesExt};
use hex_literal::hex;
use std::io::{Error, ErrorKind, Read, Result};

pub struct Header {
    pub field_size: u32,
    pub prime_size: Vec<u8>,
    pub n_wires: u32,
    pub n_pub_out: u32,
    pub n_pub_in: u32,
    pub n_prv_in: u32,
    pub n_labels: u64,
    pub n_constraints: u32,
}

pub struct R1CSFile<E: Engine> {
    pub version: u32,
    pub header: Header,
    pub constraints: Vec<Constraint<E>>,
    pub wire_mapping: Vec<u64>,
}

fn read_field<R: Read, E: Engine>(mut reader: R) -> Result<E::Fr> {
    let mut repr = E::Fr::zero().into_repr();
    repr.read_le(&mut reader)?;
    let fr = E::Fr::from_repr(repr).map_err(|e| Error::new(ErrorKind::InvalidData, e))?;
    Ok(fr)
}

fn read_header<R: Read>(mut reader: R, size: u64) -> Result<Header> {
    let field_size = reader.read_u32::<LittleEndian>()?;
    let mut prime_size = vec![0u8; field_size as usize];
    reader.read_exact(&mut prime_size)?;
    if size != 32 + field_size as u64 {
        return Err(Error::new(
            ErrorKind::InvalidData,
            "Invalid header section size",
        ));
    }

    Ok(Header {
        field_size,
        prime_size,
        n_wires: reader.read_u32::<LittleEndian>()?,
        n_pub_out: reader.read_u32::<LittleEndian>()?,
        n_pub_in: reader.read_u32::<LittleEndian>()?,
        n_prv_in: reader.read_u32::<LittleEndian>()?,
        n_labels: reader.read_u64::<LittleEndian>()?,
        n_constraints: reader.read_u32::<LittleEndian>()?,
    })
}

fn read_constraint_vec<R: Read, E: Engine>(
    mut reader: R,
    header: &Header,
) -> Result<Vec<(usize, E::Fr)>> {
    let n_vec = reader.read_u32::<LittleEndian>()? as usize;
    let mut vec = Vec::with_capacity(n_vec);
    for _ in 0..n_vec {
        vec.push((
            reader.read_u32::<LittleEndian>()? as usize,
            read_field::<&mut R, E>(&mut reader)?,
        ));
    }
    Ok(vec)
}

fn read_constraints<R: Read, E: Engine>(
    mut reader: R,
    size: u64,
    header: &Header,
) -> Result<Vec<Constraint<E>>> {
    // todo check section size
    let mut vec = Vec::with_capacity(header.n_constraints as usize);
    for _ in 0..header.n_constraints {
        vec.push((
            read_constraint_vec::<&mut R, E>(&mut reader, &header)?,
            read_constraint_vec::<&mut R, E>(&mut reader, &header)?,
            read_constraint_vec::<&mut R, E>(&mut reader, &header)?,
        ));
    }
    Ok(vec)
}

fn read_map<R: Read>(mut reader: R, size: u64, header: &Header) -> Result<Vec<u64>> {
    if size != header.n_wires as u64 * 8 {
        return Err(Error::new(
            ErrorKind::InvalidData,
            "Invalid map section size",
        ));
    }
    let mut vec = Vec::with_capacity(header.n_wires as usize);
    for _ in 0..header.n_wires {
        vec.push(reader.read_u64::<LittleEndian>()?);
    }
    if vec[0] != 0 {
        return Err(Error::new(
            ErrorKind::InvalidData,
            "Wire 0 should always be mapped to 0",
        ));
    }
    Ok(vec)
}

pub fn read<R: Read>(mut reader: R) -> Result<R1CSFile<Bn256>> {
    let mut magic = [0u8; 4];
    reader.read_exact(&mut magic)?;
    if magic != [0x72, 0x31, 0x63, 0x73] {
        // magic = "r1cs"
        return Err(Error::new(ErrorKind::InvalidData, "Invalid magic number"));
    }

    let version = reader.read_u32::<LittleEndian>()?;
    if version != 1 {
        return Err(Error::new(ErrorKind::InvalidData, "Unsupported version"));
    }

    let num_sections = reader.read_u32::<LittleEndian>()?;

    // todo: rewrite this to support different section order and unknown sections
    // todo: handle sec_size correctly
    let sec_type = reader.read_u32::<LittleEndian>()?;
    let sec_size = reader.read_u64::<LittleEndian>()?;
    let header = read_header(&mut reader, sec_size)?;
    if header.field_size != 32 {
        return Err(Error::new(
            ErrorKind::InvalidData,
            "This parser only supports 32-byte fields",
        ));
    }
    if header.prime_size != hex!("010000f093f5e1439170b97948e833285d588181b64550b829a031e1724e6430")
    {
        return Err(Error::new(
            ErrorKind::InvalidData,
            "This parser only supports bn256",
        ));
    }
    let sec_type = reader.read_u32::<LittleEndian>()?;
    let sec_size = reader.read_u64::<LittleEndian>()?;
    let constraints = read_constraints::<&mut R, Bn256>(&mut reader, sec_size, &header)?;

    let sec_type = reader.read_u32::<LittleEndian>()?;
    let sec_size = reader.read_u64::<LittleEndian>()?;
    let wire_mapping = read_map(&mut reader, sec_size, &header)?;

    Ok(R1CSFile {
        version,
        header,
        constraints,
        wire_mapping,
    })
}
