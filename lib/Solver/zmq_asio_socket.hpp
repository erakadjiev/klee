/*
 * zmq_asio_socket.hpp
 *
 *  Created on: Feb 23, 2015
 *      Author: rakadjiev
 */

#ifndef ZMQ_ASIO_SOCKET_HPP_
#define ZMQ_ASIO_SOCKET_HPP_

#include <czmq.h>
#include <boost/asio/io_service.hpp>
#include <boost/asio/posix/stream_descriptor.hpp>
#include <boost/asio/posix/stream_descriptor_service.hpp>


class non_closing_service : public boost::asio::posix::stream_descriptor_service{
public:
	explicit non_closing_service(boost::asio::io_service& io_service) : boost::asio::posix::stream_descriptor_service(io_service){}
	void destroy(typename boost::asio::posix::stream_descriptor_service::implementation_type& impl){}
	boost::system::error_code close(boost::asio::detail::reactive_descriptor_service::implementation_type& impl, boost::system::error_code& ec){
		return ec;
	}
};

class zmq_asio_socket : public boost::asio::posix::basic_stream_descriptor<non_closing_service>{
public:
	zmq_asio_socket(zsock_t* zmq_socket, boost::asio::io_service& io_service): boost::asio::posix::basic_stream_descriptor<non_closing_service>(io_service, zsock_fd(zmq_socket)), zmq_socket(zmq_socket){}
	zsock_t* get_zmq_socket(){
	  return zmq_socket;
	}
private:
	zsock_t* zmq_socket;
};

#endif /* ZMQ_ASIO_SOCKET_HPP_ */
