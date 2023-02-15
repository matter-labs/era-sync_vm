macro_rules! width_marker_impl {
	( $visibility:vis struct $name:ident ( $width:tt ) ) => {
        #[derive(Clone, Copy)]
        $visibility struct $name;

        impl WidthMarker for $name {
            const WIDTH: usize = $width;
        }
    }
}

pub trait WidthMarker: Sized + Send + Sync + Clone + Copy {
    const WIDTH: usize;
}

width_marker_impl!(pub struct U8(8));
width_marker_impl!(pub struct U16(16));
width_marker_impl!(pub struct U24(24));
width_marker_impl!(pub struct U32(32));
width_marker_impl!(pub struct U48(48));
width_marker_impl!(pub struct U64(64));
width_marker_impl!(pub struct U128(128));
width_marker_impl!(pub struct U160(160));
width_marker_impl!(pub struct U163(163));
width_marker_impl!(pub struct U176(176));
width_marker_impl!(pub struct U178(178));
width_marker_impl!(pub struct U192(192));
width_marker_impl!(pub struct U224(224));
