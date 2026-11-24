-module(tazuna_launch_ffi).
-export([argv/0, getenv/1, spawn/2, exit/1]).

argv() ->
    [unicode:characters_to_binary(A) || A <- init:get_plain_arguments()].

getenv(Name) ->
    case os:getenv(unicode:characters_to_list(Name)) of
        false -> {error, nil};
        Value -> {ok, unicode:characters_to_binary(Value)}
    end.

spawn(Path, Args) ->
    Options = [{args, [unicode:characters_to_list(A) || A <- Args]},
               {line, 65536}, exit_status, binary, use_stdio],
    try open_port({spawn_executable, unicode:characters_to_list(Path)}, Options) of
        Port -> {ok, relay(Port, [])}
    catch
        error:Reason ->
            {error, unicode:characters_to_binary(io_lib:format("~p", [Reason]))}
    end.

%% Prints whole lines only, so a UTF-8 sequence split across reads stays intact.
relay(Port, Partial) ->
    receive
        {Port, {data, {noeol, Part}}} ->
            relay(Port, [Partial, Part]);
        {Port, {data, {eol, Line}}} ->
            io:put_chars([Partial, Line, $\n]),
            relay(Port, []);
        {Port, {exit_status, Status}} ->
            case iolist_size(Partial) of
                0 -> ok;
                _ -> io:put_chars(Partial)
            end,
            Status
    end.

exit(Code) ->
    erlang:halt(Code).
